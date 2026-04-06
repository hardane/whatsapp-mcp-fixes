package main

import (
	"bufio"
	"bytes"
	"context"
	"database/sql"
	"encoding/binary"
	"encoding/json"
	"fmt"
	"log"
	"math"
	"math/rand"
	"net/http"
	"os"
	"os/signal"
	"path/filepath"
	"reflect"
	"strings"
	"sync"
	"sync/atomic"
	"syscall"
	"time"

	_ "github.com/mattn/go-sqlite3"
	"github.com/mdp/qrterminal"

	"go.mau.fi/whatsmeow"
	"go.mau.fi/whatsmeow/appstate"
	waProto "go.mau.fi/whatsmeow/binary/proto"
	waCommon "go.mau.fi/whatsmeow/proto/waCommon"
	waCompanionReg "go.mau.fi/whatsmeow/proto/waCompanionReg"
	"go.mau.fi/whatsmeow/store"
	"go.mau.fi/whatsmeow/store/sqlstore"
	"go.mau.fi/whatsmeow/types"
	"go.mau.fi/whatsmeow/types/events"
	waLog "go.mau.fi/whatsmeow/util/log"
	"google.golang.org/protobuf/proto"
)

// Package-level app state recovery tracking.
// HTTP handlers check these to avoid sending mutations while recovery is in progress.
var pendingRecoveryMu sync.Mutex
var pendingRecovery = make(map[appstate.WAPatchName]bool)


// recoveryDone is signaled when AppStateSyncComplete fires with Recovery=true.
// Used by /api/test-recovery to wait for the phone's response.
var recoveryDone = make(chan appstate.WAPatchName, 4)


// syncLog writes structured debug data to store/sync-debug.log so we can
// analyze sync behavior without scrolling through noisy console output.
var syncLog *log.Logger

// Running totals for sync debug logging (atomically updated).
var totalHSyncEvents int64
var totalHSyncConvs int64
var totalHSyncMsgsStored int64
var totalHSyncMsgsSkipped int64
var totalAppStateArchive int64
var totalAppStateArchiveTrue int64
var totalAppStateArchiveFalse int64
var totalJIDResolveOK int64
var totalJIDResolveFail int64

func initSyncDebugLog() *os.File {
	f, err := os.OpenFile("store/sync-debug.log", os.O_CREATE|os.O_WRONLY|os.O_TRUNC, 0644)
	if err != nil {
		fmt.Printf("WARNING: could not open sync-debug.log: %v\n", err)
		syncLog = log.New(os.Stdout, "[SYNC] ", log.Ltime)
		return nil
	}
	syncLog = log.New(f, "", log.Ltime)
	syncLog.Println("=== Sync debug log started ===")
	return f
}

// Message represents a chat message for our client
type Message struct {
	Time      time.Time
	Sender    string
	Content   string
	IsFromMe  bool
	MediaType string
	Filename  string
}

// Database handler for storing message history
type MessageStore struct {
	db       *sql.DB
	lidStore store.LIDStore
}

// SetLIDStore sets the LID↔PN mapping store so NormalizeJID can resolve JIDs.
func (s *MessageStore) SetLIDStore(ls store.LIDStore) {
	s.lidStore = ls
}

// NormalizeJID converts a types.JID to the canonical string used as DB key.
// For individual chats (s.whatsapp.net / lid), it prefers the LID form.
// Groups (@g.us) and other JID types are returned as-is.
func (s *MessageStore) NormalizeJID(jid types.JID) string {
	raw := jid.String()

	if s.lidStore == nil {
		if syncLog != nil {
			syncLog.Printf("[JID] %s → PASSTHROUGH (no LID store)", raw)
		}
		return raw
	}

	switch jid.Server {
	case "s.whatsapp.net":
		// Phone number → try to resolve to LID
		lidJID, err := s.lidStore.GetLIDForPN(context.Background(), jid)
		if err == nil && !lidJID.IsEmpty() {
			atomic.AddInt64(&totalJIDResolveOK, 1)
			if syncLog != nil {
				syncLog.Printf("[JID] %s → %s (OK)", raw, lidJID.String())
			}
			return lidJID.String()
		}
		atomic.AddInt64(&totalJIDResolveFail, 1)
		if syncLog != nil {
			syncLog.Printf("[JID] %s → FAILED (err=%v empty=%v)", raw, err, lidJID.IsEmpty())
		}
	case "lid":
		// Already a LID — use as-is
	}

	return raw
}

// Initialize message store
func NewMessageStore() (*MessageStore, error) {
	// Create directory for database if it doesn't exist
	if err := os.MkdirAll("store", 0755); err != nil {
		return nil, fmt.Errorf("failed to create store directory: %v", err)
	}

	// Open SQLite database for messages
	db, err := sql.Open("sqlite3", "file:store/messages.db?_foreign_keys=on&_journal_mode=WAL&_busy_timeout=5000")
	if err != nil {
		return nil, fmt.Errorf("failed to open message database: %v", err)
	}

	// Create tables if they don't exist
	_, err = db.Exec(`
		CREATE TABLE IF NOT EXISTS chats (
			jid TEXT PRIMARY KEY,
			name TEXT,
			last_message_time TIMESTAMP
		);
		
		CREATE TABLE IF NOT EXISTS messages (
			id TEXT,
			chat_jid TEXT,
			sender TEXT,
			content TEXT,
			timestamp TIMESTAMP,
			is_from_me BOOLEAN,
			media_type TEXT,
			filename TEXT,
			url TEXT,
			media_key BLOB,
			file_sha256 BLOB,
			file_enc_sha256 BLOB,
			file_length INTEGER,
			PRIMARY KEY (id, chat_jid),
			FOREIGN KEY (chat_jid) REFERENCES chats(jid)
		);
	`)
	if err != nil {
		db.Close()
		return nil, fmt.Errorf("failed to create tables: %v", err)
	}

	// Idempotent migrations — safe to run on every startup
	migrations := []string{
		"ALTER TABLE chats ADD COLUMN is_archived BOOLEAN DEFAULT FALSE",
		"ALTER TABLE chats ADD COLUMN unread_count INTEGER DEFAULT 0",
		"ALTER TABLE messages ADD COLUMN is_read BOOLEAN DEFAULT FALSE",
		"ALTER TABLE chats ADD COLUMN is_pinned BOOLEAN DEFAULT FALSE",
		"ALTER TABLE chats ADD COLUMN mute_end_time INTEGER DEFAULT 0",
	}
	for _, migration := range migrations {
		_, err := db.Exec(migration)
		if err != nil && !strings.Contains(err.Error(), "duplicate column name") {
			db.Close()
			return nil, fmt.Errorf("migration failed: %v", err)
		}
	}

	return &MessageStore{db: db}, nil
}

// Close the database connection
func (store *MessageStore) Close() error {
	return store.db.Close()
}

// Store a chat in the database (preserves is_archived and unread_count on update)
func (store *MessageStore) StoreChat(jid, name string, lastMessageTime time.Time) error {
	_, err := store.db.Exec(
		`INSERT INTO chats (jid, name, last_message_time) VALUES (?, ?, ?)
		 ON CONFLICT(jid) DO UPDATE SET name = excluded.name, last_message_time = excluded.last_message_time`,
		jid, name, lastMessageTime,
	)
	return err
}

// StoreChatFromHistory stores a chat discovered via history sync.
// Sets all chat metadata from the Conversation proto. On conflict, only
// updates name and timestamp — metadata fields (archive, pin, mute,
// unread) are NOT overwritten so that app state or real-time events
// that arrived earlier are preserved.
func (store *MessageStore) StoreChatFromHistory(jid, name string, lastMessageTime time.Time, archived bool, pinned bool, muteEndTime int64, unreadCount int) error {
	_, err := store.db.Exec(
		`INSERT INTO chats (jid, name, last_message_time, is_archived, is_pinned, mute_end_time, unread_count)
		 VALUES (?, ?, ?, ?, ?, ?, ?)
		 ON CONFLICT(jid) DO UPDATE SET name = excluded.name, last_message_time = excluded.last_message_time`,
		jid, name, lastMessageTime, archived, pinned, muteEndTime, unreadCount,
	)
	return err
}

// Store a message in the database
func (store *MessageStore) StoreMessage(id, chatJID, sender, content string, timestamp time.Time, isFromMe bool,
	mediaType, filename, url string, mediaKey, fileSHA256, fileEncSHA256 []byte, fileLength uint64) error {
	// Only store if there's actual content or media
	if content == "" && mediaType == "" {
		return nil
	}

	_, err := store.db.Exec(
		`INSERT OR REPLACE INTO messages
		(id, chat_jid, sender, content, timestamp, is_from_me, media_type, filename, url, media_key, file_sha256, file_enc_sha256, file_length)
		VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)`,
		id, chatJID, sender, content, timestamp, isFromMe, mediaType, filename, url, mediaKey, fileSHA256, fileEncSHA256, fileLength,
	)
	if err != nil {
		return err
	}

	// Increment unread count for incoming messages
	if !isFromMe {
		_, err = store.db.Exec("UPDATE chats SET unread_count = unread_count + 1 WHERE jid = ?", chatJID)
	}
	return err
}

// StoreHistoryMessage stores a message from history sync without touching unread counts,
// and sets is_read based on whether the message is within the unread window.
func (store *MessageStore) StoreHistoryMessage(id, chatJID, sender, content string, timestamp time.Time, isFromMe bool,
	mediaType, filename, url string, mediaKey, fileSHA256, fileEncSHA256 []byte, fileLength uint64, isRead bool) error {
	if content == "" && mediaType == "" {
		return nil
	}

	_, err := store.db.Exec(
		`INSERT OR REPLACE INTO messages
		(id, chat_jid, sender, content, timestamp, is_from_me, media_type, filename, url, media_key, file_sha256, file_enc_sha256, file_length, is_read)
		VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)`,
		id, chatJID, sender, content, timestamp, isFromMe, mediaType, filename, url, mediaKey, fileSHA256, fileEncSHA256, fileLength, isRead,
	)
	return err
}

// SetChatArchived updates the archive status of a chat (upserts so app state events
// that arrive before history sync are not lost)
func (store *MessageStore) SetChatArchived(chatJID string, archived bool) error {
	_, err := store.db.Exec(
		`INSERT INTO chats (jid, is_archived) VALUES (?, ?)
		 ON CONFLICT(jid) DO UPDATE SET is_archived = excluded.is_archived`,
		chatJID, archived,
	)
	return err
}

// SetChatPinned updates the pin status of a chat (upserts so app state events
// that arrive before history sync are not lost)
func (store *MessageStore) SetChatPinned(chatJID string, pinned bool) error {
	_, err := store.db.Exec(
		`INSERT INTO chats (jid, is_pinned) VALUES (?, ?)
		 ON CONFLICT(jid) DO UPDATE SET is_pinned = excluded.is_pinned`,
		chatJID, pinned,
	)
	return err
}

// SetChatMuted updates the mute end time of a chat (upserts so app state events
// that arrive before history sync are not lost). muteEndTimestamp=0 means not muted.
func (store *MessageStore) SetChatMuted(chatJID string, muteEndTimestamp int64) error {
	_, err := store.db.Exec(
		`INSERT INTO chats (jid, mute_end_time) VALUES (?, ?)
		 ON CONFLICT(jid) DO UPDATE SET mute_end_time = excluded.mute_end_time`,
		chatJID, muteEndTimestamp,
	)
	return err
}

// UpdateChatName updates the name for a chat, but only if the current name is
// missing or looks like a phone number (all digits). This prevents overwriting
// a real name with a push name, while ensuring phone-number placeholders get replaced.
func (store *MessageStore) UpdateChatName(chatJID, name string) error {
	_, err := store.db.Exec(
		`UPDATE chats SET name = ?
		 WHERE jid = ? AND (name IS NULL OR name = '' OR name NOT GLOB '*[^0-9]*')`,
		name, chatJID,
	)
	return err
}

// MarkChatAsRead marks all incoming messages in a chat as read and resets unread count
func (store *MessageStore) MarkChatAsRead(chatJID string) error {
	_, err := store.db.Exec("UPDATE messages SET is_read = TRUE WHERE chat_jid = ? AND is_from_me = FALSE AND is_read = FALSE", chatJID)
	if err != nil {
		return err
	}
	_, err = store.db.Exec(
		`INSERT INTO chats (jid, unread_count) VALUES (?, 0)
		 ON CONFLICT(jid) DO UPDATE SET unread_count = 0`,
		chatJID,
	)
	return err
}

// MarkChatAsUnread sets the unread count sentinel to indicate manually marked unread
func (store *MessageStore) MarkChatAsUnread(chatJID string) error {
	_, err := store.db.Exec(
		`INSERT INTO chats (jid, unread_count) VALUES (?, -1)
		 ON CONFLICT(jid) DO UPDATE SET unread_count = -1`,
		chatJID,
	)
	return err
}

// MarkMessagesAsRead marks specific messages as read and recalculates unread count
func (store *MessageStore) MarkMessagesAsRead(chatJID string, messageIDs []string) error {
	if len(messageIDs) == 0 {
		return nil
	}
	// Build placeholders for IN clause
	placeholders := strings.Repeat("?,", len(messageIDs))
	placeholders = placeholders[:len(placeholders)-1] // trim trailing comma
	args := make([]interface{}, 0, len(messageIDs)+1)
	args = append(args, chatJID)
	for _, id := range messageIDs {
		args = append(args, id)
	}
	_, err := store.db.Exec(
		fmt.Sprintf("UPDATE messages SET is_read = TRUE WHERE chat_jid = ? AND id IN (%s)", placeholders),
		args...,
	)
	if err != nil {
		return err
	}
	// Recalculate unread count
	_, err = store.db.Exec(
		"UPDATE chats SET unread_count = (SELECT COUNT(*) FROM messages WHERE chat_jid = ? AND is_from_me = FALSE AND is_read = FALSE) WHERE jid = ?",
		chatJID, chatJID,
	)
	return err
}

// GetLastMessage returns the last message in a chat for building MessageKey
func (store *MessageStore) GetLastMessage(chatJID string) (id string, sender string, timestamp time.Time, isFromMe bool, err error) {
	err = store.db.QueryRow(
		"SELECT id, sender, timestamp, is_from_me FROM messages WHERE chat_jid = ? ORDER BY timestamp DESC LIMIT 1",
		chatJID,
	).Scan(&id, &sender, &timestamp, &isFromMe)
	return
}

// GetUnreadMessagesBySender returns unread incoming message IDs grouped by sender for a chat
func (store *MessageStore) GetUnreadMessagesBySender(chatJID string) (map[string][]string, error) {
	rows, err := store.db.Query(
		"SELECT id, sender FROM messages WHERE chat_jid = ? AND is_from_me = FALSE AND is_read = FALSE",
		chatJID,
	)
	if err != nil {
		return nil, err
	}
	defer rows.Close()
	result := make(map[string][]string)
	for rows.Next() {
		var msgID, sender string
		if err := rows.Scan(&msgID, &sender); err != nil {
			return nil, err
		}
		result[sender] = append(result[sender], msgID)
	}
	return result, nil
}

// Get messages from a chat
func (store *MessageStore) GetMessages(chatJID string, limit int) ([]Message, error) {
	rows, err := store.db.Query(
		"SELECT sender, content, timestamp, is_from_me, media_type, filename FROM messages WHERE chat_jid = ? ORDER BY timestamp DESC LIMIT ?",
		chatJID, limit,
	)
	if err != nil {
		return nil, err
	}
	defer rows.Close()

	var messages []Message
	for rows.Next() {
		var msg Message
		var timestamp time.Time
		err := rows.Scan(&msg.Sender, &msg.Content, &timestamp, &msg.IsFromMe, &msg.MediaType, &msg.Filename)
		if err != nil {
			return nil, err
		}
		msg.Time = timestamp
		messages = append(messages, msg)
	}

	return messages, nil
}

// Get all chats
func (store *MessageStore) GetChats() (map[string]time.Time, error) {
	rows, err := store.db.Query("SELECT jid, last_message_time FROM chats ORDER BY last_message_time DESC")
	if err != nil {
		return nil, err
	}
	defer rows.Close()

	chats := make(map[string]time.Time)
	for rows.Next() {
		var jid string
		var lastMessageTime time.Time
		err := rows.Scan(&jid, &lastMessageTime)
		if err != nil {
			return nil, err
		}
		chats[jid] = lastMessageTime
	}

	return chats, nil
}

// Extract text content from a message
func extractTextContent(msg *waProto.Message) string {
	if msg == nil {
		return ""
	}

	// Try to get text content
	if text := msg.GetConversation(); text != "" {
		return text
	} else if extendedText := msg.GetExtendedTextMessage(); extendedText != nil {
		return extendedText.GetText()
	}

	// For now, we're ignoring non-text messages
	return ""
}

// SendMessageResponse represents the response for the send message API
type SendMessageResponse struct {
	Success bool   `json:"success"`
	Message string `json:"message"`
}

// SendMessageRequest represents the request body for the send message API
type SendMessageRequest struct {
	Recipient string `json:"recipient"`
	Message   string `json:"message"`
	MediaPath string `json:"media_path,omitempty"`
}

// Function to send a WhatsApp message
func sendWhatsAppMessage(client *whatsmeow.Client, recipient string, message string, mediaPath string) (bool, string) {
	if !client.IsConnected() {
		return false, "Not connected to WhatsApp"
	}

	// Create JID for recipient
	var recipientJID types.JID
	var err error

	// Check if recipient is a JID
	isJID := strings.Contains(recipient, "@")

	if isJID {
		// Parse the JID string
		recipientJID, err = types.ParseJID(recipient)
		if err != nil {
			return false, fmt.Sprintf("Error parsing JID: %v", err)
		}
	} else {
		// Create JID from phone number
		recipientJID = types.JID{
			User:   recipient,
			Server: "s.whatsapp.net", // For personal chats
		}
	}

	msg := &waProto.Message{}

	// Check if we have media to send
	if mediaPath != "" {
		// Read media file
		mediaData, err := os.ReadFile(mediaPath)
		if err != nil {
			return false, fmt.Sprintf("Error reading media file: %v", err)
		}

		// Determine media type and mime type based on file extension
		fileExt := strings.ToLower(mediaPath[strings.LastIndex(mediaPath, ".")+1:])
		var mediaType whatsmeow.MediaType
		var mimeType string

		// Handle different media types
		switch fileExt {
		// Image types
		case "jpg", "jpeg":
			mediaType = whatsmeow.MediaImage
			mimeType = "image/jpeg"
		case "png":
			mediaType = whatsmeow.MediaImage
			mimeType = "image/png"
		case "gif":
			mediaType = whatsmeow.MediaImage
			mimeType = "image/gif"
		case "webp":
			mediaType = whatsmeow.MediaImage
			mimeType = "image/webp"

		// Audio types
		case "ogg":
			mediaType = whatsmeow.MediaAudio
			mimeType = "audio/ogg; codecs=opus"

		// Video types
		case "mp4":
			mediaType = whatsmeow.MediaVideo
			mimeType = "video/mp4"
		case "avi":
			mediaType = whatsmeow.MediaVideo
			mimeType = "video/avi"
		case "mov":
			mediaType = whatsmeow.MediaVideo
			mimeType = "video/quicktime"

		// Document types (for any other file type)
		default:
			mediaType = whatsmeow.MediaDocument
			mimeType = "application/octet-stream"
		}

		// Upload media to WhatsApp servers
		resp, err := client.Upload(context.Background(), mediaData, mediaType)
		if err != nil {
			return false, fmt.Sprintf("Error uploading media: %v", err)
		}

		fmt.Println("Media uploaded", resp)

		// Create the appropriate message type based on media type
		switch mediaType {
		case whatsmeow.MediaImage:
			msg.ImageMessage = &waProto.ImageMessage{
				Caption:       proto.String(message),
				Mimetype:      proto.String(mimeType),
				URL:           &resp.URL,
				DirectPath:    &resp.DirectPath,
				MediaKey:      resp.MediaKey,
				FileEncSHA256: resp.FileEncSHA256,
				FileSHA256:    resp.FileSHA256,
				FileLength:    &resp.FileLength,
			}
		case whatsmeow.MediaAudio:
			// Handle ogg audio files
			var seconds uint32 = 30 // Default fallback
			var waveform []byte = nil

			// Try to analyze the ogg file
			if strings.Contains(mimeType, "ogg") {
				analyzedSeconds, analyzedWaveform, err := analyzeOggOpus(mediaData)
				if err == nil {
					seconds = analyzedSeconds
					waveform = analyzedWaveform
				} else {
					return false, fmt.Sprintf("Failed to analyze Ogg Opus file: %v", err)
				}
			} else {
				fmt.Printf("Not an Ogg Opus file: %s\n", mimeType)
			}

			msg.AudioMessage = &waProto.AudioMessage{
				Mimetype:      proto.String(mimeType),
				URL:           &resp.URL,
				DirectPath:    &resp.DirectPath,
				MediaKey:      resp.MediaKey,
				FileEncSHA256: resp.FileEncSHA256,
				FileSHA256:    resp.FileSHA256,
				FileLength:    &resp.FileLength,
				Seconds:       proto.Uint32(seconds),
				PTT:           proto.Bool(true),
				Waveform:      waveform,
			}
		case whatsmeow.MediaVideo:
			msg.VideoMessage = &waProto.VideoMessage{
				Caption:       proto.String(message),
				Mimetype:      proto.String(mimeType),
				URL:           &resp.URL,
				DirectPath:    &resp.DirectPath,
				MediaKey:      resp.MediaKey,
				FileEncSHA256: resp.FileEncSHA256,
				FileSHA256:    resp.FileSHA256,
				FileLength:    &resp.FileLength,
			}
		case whatsmeow.MediaDocument:
			msg.DocumentMessage = &waProto.DocumentMessage{
				Title:         proto.String(mediaPath[strings.LastIndex(mediaPath, "/")+1:]),
				Caption:       proto.String(message),
				Mimetype:      proto.String(mimeType),
				URL:           &resp.URL,
				DirectPath:    &resp.DirectPath,
				MediaKey:      resp.MediaKey,
				FileEncSHA256: resp.FileEncSHA256,
				FileSHA256:    resp.FileSHA256,
				FileLength:    &resp.FileLength,
			}
		}
	} else {
		msg.Conversation = proto.String(message)
	}

	// Send message
	_, err = client.SendMessage(context.Background(), recipientJID, msg)

	if err != nil {
		return false, fmt.Sprintf("Error sending message: %v", err)
	}

	return true, fmt.Sprintf("Message sent to %s", recipient)
}

// Extract media info from a message
func extractMediaInfo(msg *waProto.Message) (mediaType string, filename string, url string, mediaKey []byte, fileSHA256 []byte, fileEncSHA256 []byte, fileLength uint64) {
	if msg == nil {
		return "", "", "", nil, nil, nil, 0
	}

	// Check for image message
	if img := msg.GetImageMessage(); img != nil {
		return "image", "image_" + time.Now().Format("20060102_150405") + ".jpg",
			img.GetURL(), img.GetMediaKey(), img.GetFileSHA256(), img.GetFileEncSHA256(), img.GetFileLength()
	}

	// Check for video message
	if vid := msg.GetVideoMessage(); vid != nil {
		return "video", "video_" + time.Now().Format("20060102_150405") + ".mp4",
			vid.GetURL(), vid.GetMediaKey(), vid.GetFileSHA256(), vid.GetFileEncSHA256(), vid.GetFileLength()
	}

	// Check for audio message
	if aud := msg.GetAudioMessage(); aud != nil {
		return "audio", "audio_" + time.Now().Format("20060102_150405") + ".ogg",
			aud.GetURL(), aud.GetMediaKey(), aud.GetFileSHA256(), aud.GetFileEncSHA256(), aud.GetFileLength()
	}

	// Check for document message
	if doc := msg.GetDocumentMessage(); doc != nil {
		filename := doc.GetFileName()
		if filename == "" {
			filename = "document_" + time.Now().Format("20060102_150405")
		}
		return "document", filename,
			doc.GetURL(), doc.GetMediaKey(), doc.GetFileSHA256(), doc.GetFileEncSHA256(), doc.GetFileLength()
	}

	return "", "", "", nil, nil, nil, 0
}

// Handle regular incoming messages with media support
func handleMessage(client *whatsmeow.Client, messageStore *MessageStore, msg *events.Message, logger waLog.Logger) {
	// Save message to database — normalize JID to LID for individual chats
	chatJID := messageStore.NormalizeJID(msg.Info.Chat)
	sender := msg.Info.Sender.User

	// Get appropriate chat name (pass nil for conversation since we don't have one for regular messages)
	name := GetChatName(client, messageStore, msg.Info.Chat, chatJID, nil, sender, logger)

	// Update chat in database with the message timestamp (keeps last message time updated)
	err := messageStore.StoreChat(chatJID, name, msg.Info.Timestamp)
	if err != nil {
		logger.Warnf("Failed to store chat: %v", err)
	}

	// Extract text content
	content := extractTextContent(msg.Message)

	// Extract media info
	mediaType, filename, url, mediaKey, fileSHA256, fileEncSHA256, fileLength := extractMediaInfo(msg.Message)

	// Skip if there's no content and no media
	if content == "" && mediaType == "" {
		return
	}

	// Store message in database
	err = messageStore.StoreMessage(
		msg.Info.ID,
		chatJID,
		sender,
		content,
		msg.Info.Timestamp,
		msg.Info.IsFromMe,
		mediaType,
		filename,
		url,
		mediaKey,
		fileSHA256,
		fileEncSHA256,
		fileLength,
	)

	if err != nil {
		logger.Warnf("Failed to store message: %v", err)
	} else {
		// Log message reception
		timestamp := msg.Info.Timestamp.Format("2006-01-02 15:04:05")
		direction := "←"
		if msg.Info.IsFromMe {
			direction = "→"
		}

		// Log based on message type
		if mediaType != "" {
			fmt.Printf("[%s] %s %s: [%s: %s] %s\n", timestamp, direction, sender, mediaType, filename, content)
		} else if content != "" {
			fmt.Printf("[%s] %s %s: %s\n", timestamp, direction, sender, content)
		}
	}
}

// DownloadMediaRequest represents the request body for the download media API
type DownloadMediaRequest struct {
	MessageID string `json:"message_id"`
	ChatJID   string `json:"chat_jid"`
}

// DownloadMediaResponse represents the response for the download media API
type DownloadMediaResponse struct {
	Success   bool   `json:"success"`
	Message   string `json:"message"`
	Filename  string `json:"filename,omitempty"`
	Path      string `json:"path,omitempty"`
	MediaType string `json:"media_type,omitempty"`
}

// ArchiveRequest represents the request body for the archive chat API
type ArchiveRequest struct {
	ChatJID string `json:"chat_jid"`
	Archive bool   `json:"archive"`
}

// MarkReadRequest represents the request body for the mark read API
type MarkReadRequest struct {
	ChatJID string `json:"chat_jid"`
}

// buildMessageKey constructs a MessageKey from the last message in a chat
func buildMessageKey(chatJID, messageID string, isFromMe bool) *waCommon.MessageKey {
	return &waCommon.MessageKey{
		RemoteJID: proto.String(chatJID),
		FromMe:    proto.Bool(isFromMe),
		ID:        proto.String(messageID),
	}
}

// Store additional media info in the database
func (store *MessageStore) StoreMediaInfo(id, chatJID, url string, mediaKey, fileSHA256, fileEncSHA256 []byte, fileLength uint64) error {
	_, err := store.db.Exec(
		"UPDATE messages SET url = ?, media_key = ?, file_sha256 = ?, file_enc_sha256 = ?, file_length = ? WHERE id = ? AND chat_jid = ?",
		url, mediaKey, fileSHA256, fileEncSHA256, fileLength, id, chatJID,
	)
	return err
}

// Get media info from the database
func (store *MessageStore) GetMediaInfo(id, chatJID string) (string, string, string, []byte, []byte, []byte, uint64, error) {
	var mediaType, filename, url string
	var mediaKey, fileSHA256, fileEncSHA256 []byte
	var fileLength uint64

	err := store.db.QueryRow(
		"SELECT media_type, filename, url, media_key, file_sha256, file_enc_sha256, file_length FROM messages WHERE id = ? AND chat_jid = ?",
		id, chatJID,
	).Scan(&mediaType, &filename, &url, &mediaKey, &fileSHA256, &fileEncSHA256, &fileLength)

	return mediaType, filename, url, mediaKey, fileSHA256, fileEncSHA256, fileLength, err
}

// MediaDownloader implements the whatsmeow.DownloadableMessage interface
type MediaDownloader struct {
	URL           string
	DirectPath    string
	MediaKey      []byte
	FileLength    uint64
	FileSHA256    []byte
	FileEncSHA256 []byte
	MediaType     whatsmeow.MediaType
}

// GetDirectPath implements the DownloadableMessage interface
func (d *MediaDownloader) GetDirectPath() string {
	return d.DirectPath
}

// GetURL implements the DownloadableMessage interface
func (d *MediaDownloader) GetURL() string {
	return d.URL
}

// GetMediaKey implements the DownloadableMessage interface
func (d *MediaDownloader) GetMediaKey() []byte {
	return d.MediaKey
}

// GetFileLength implements the DownloadableMessage interface
func (d *MediaDownloader) GetFileLength() uint64 {
	return d.FileLength
}

// GetFileSHA256 implements the DownloadableMessage interface
func (d *MediaDownloader) GetFileSHA256() []byte {
	return d.FileSHA256
}

// GetFileEncSHA256 implements the DownloadableMessage interface
func (d *MediaDownloader) GetFileEncSHA256() []byte {
	return d.FileEncSHA256
}

// GetMediaType implements the DownloadableMessage interface
func (d *MediaDownloader) GetMediaType() whatsmeow.MediaType {
	return d.MediaType
}

// Function to download media from a message
func downloadMedia(client *whatsmeow.Client, messageStore *MessageStore, messageID, chatJID string) (bool, string, string, string, error) {
	// Query the database for the message
	var mediaType, filename, url string
	var mediaKey, fileSHA256, fileEncSHA256 []byte
	var fileLength uint64
	var err error

	// First, check if we already have this file
	chatDir := fmt.Sprintf("store/%s", strings.ReplaceAll(chatJID, ":", "_"))
	localPath := ""

	// Get media info from the database
	mediaType, filename, url, mediaKey, fileSHA256, fileEncSHA256, fileLength, err = messageStore.GetMediaInfo(messageID, chatJID)

	if err != nil {
		// Try to get basic info if extended info isn't available
		err = messageStore.db.QueryRow(
			"SELECT media_type, filename FROM messages WHERE id = ? AND chat_jid = ?",
			messageID, chatJID,
		).Scan(&mediaType, &filename)

		if err != nil {
			return false, "", "", "", fmt.Errorf("failed to find message: %v", err)
		}
	}

	// Check if this is a media message
	if mediaType == "" {
		return false, "", "", "", fmt.Errorf("not a media message")
	}

	// Create directory for the chat if it doesn't exist
	if err := os.MkdirAll(chatDir, 0755); err != nil {
		return false, "", "", "", fmt.Errorf("failed to create chat directory: %v", err)
	}

	// Generate a local path for the file
	localPath = fmt.Sprintf("%s/%s", chatDir, filename)

	// Get absolute path
	absPath, err := filepath.Abs(localPath)
	if err != nil {
		return false, "", "", "", fmt.Errorf("failed to get absolute path: %v", err)
	}

	// Check if file already exists
	if _, err := os.Stat(localPath); err == nil {
		// File exists, return it
		return true, mediaType, filename, absPath, nil
	}

	// If we don't have all the media info we need, we can't download
	if url == "" || len(mediaKey) == 0 || len(fileSHA256) == 0 || len(fileEncSHA256) == 0 || fileLength == 0 {
		return false, "", "", "", fmt.Errorf("incomplete media information for download")
	}

	fmt.Printf("Attempting to download media for message %s in chat %s...\n", messageID, chatJID)

	// Extract direct path from URL
	directPath := extractDirectPathFromURL(url)

	// Create a downloader that implements DownloadableMessage
	var waMediaType whatsmeow.MediaType
	switch mediaType {
	case "image":
		waMediaType = whatsmeow.MediaImage
	case "video":
		waMediaType = whatsmeow.MediaVideo
	case "audio":
		waMediaType = whatsmeow.MediaAudio
	case "document":
		waMediaType = whatsmeow.MediaDocument
	default:
		return false, "", "", "", fmt.Errorf("unsupported media type: %s", mediaType)
	}

	downloader := &MediaDownloader{
		URL:           url,
		DirectPath:    directPath,
		MediaKey:      mediaKey,
		FileLength:    fileLength,
		FileSHA256:    fileSHA256,
		FileEncSHA256: fileEncSHA256,
		MediaType:     waMediaType,
	}

	// Download the media using whatsmeow client
	mediaData, err := client.Download(context.Background(), downloader)
	if err != nil {
		return false, "", "", "", fmt.Errorf("failed to download media: %v", err)
	}

	// Save the downloaded media to file
	if err := os.WriteFile(localPath, mediaData, 0644); err != nil {
		return false, "", "", "", fmt.Errorf("failed to save media file: %v", err)
	}

	fmt.Printf("Successfully downloaded %s media to %s (%d bytes)\n", mediaType, absPath, len(mediaData))
	return true, mediaType, filename, absPath, nil
}

// Extract direct path from a WhatsApp media URL
func extractDirectPathFromURL(url string) string {
	// The direct path is typically in the URL, we need to extract it
	// Example URL: https://mmg.whatsapp.net/v/t62.7118-24/13812002_698058036224062_3424455886509161511_n.enc?ccb=11-4&oh=...

	// Find the path part after the domain
	parts := strings.SplitN(url, ".net/", 2)
	if len(parts) < 2 {
		return url // Return original URL if parsing fails
	}

	pathPart := parts[1]

	// Remove query parameters
	pathPart = strings.SplitN(pathPart, "?", 2)[0]

	// Create proper direct path format
	return "/" + pathPart
}

// Start a REST API server to expose the WhatsApp client functionality
func startRESTServer(client *whatsmeow.Client, messageStore *MessageStore, port int) {
	// Handler for sending messages
	http.HandleFunc("/api/send", func(w http.ResponseWriter, r *http.Request) {
		// Only allow POST requests
		if r.Method != http.MethodPost {
			http.Error(w, "Method not allowed", http.StatusMethodNotAllowed)
			return
		}

		// Parse the request body
		var req SendMessageRequest
		if err := json.NewDecoder(r.Body).Decode(&req); err != nil {
			http.Error(w, "Invalid request format", http.StatusBadRequest)
			return
		}

		// Validate request
		if req.Recipient == "" {
			http.Error(w, "Recipient is required", http.StatusBadRequest)
			return
		}

		if req.Message == "" && req.MediaPath == "" {
			http.Error(w, "Message or media path is required", http.StatusBadRequest)
			return
		}

		fmt.Println("Received request to send message", req.Message, req.MediaPath)

		// Send the message
		success, message := sendWhatsAppMessage(client, req.Recipient, req.Message, req.MediaPath)
		fmt.Println("Message sent", success, message)
		// Set response headers
		w.Header().Set("Content-Type", "application/json")

		// Set appropriate status code
		if !success {
			w.WriteHeader(http.StatusInternalServerError)
		}

		// Send response
		json.NewEncoder(w).Encode(SendMessageResponse{
			Success: success,
			Message: message,
		})
	})

	// Handler for downloading media
	http.HandleFunc("/api/download", func(w http.ResponseWriter, r *http.Request) {
		// Only allow POST requests
		if r.Method != http.MethodPost {
			http.Error(w, "Method not allowed", http.StatusMethodNotAllowed)
			return
		}

		// Parse the request body
		var req DownloadMediaRequest
		if err := json.NewDecoder(r.Body).Decode(&req); err != nil {
			http.Error(w, "Invalid request format", http.StatusBadRequest)
			return
		}

		// Validate request
		if req.MessageID == "" || req.ChatJID == "" {
			http.Error(w, "Message ID and Chat JID are required", http.StatusBadRequest)
			return
		}

		// Download the media
		success, mediaType, filename, path, err := downloadMedia(client, messageStore, req.MessageID, req.ChatJID)

		// Set response headers
		w.Header().Set("Content-Type", "application/json")

		// Handle download result
		if !success || err != nil {
			errMsg := "Unknown error"
			if err != nil {
				errMsg = err.Error()
			}

			w.WriteHeader(http.StatusInternalServerError)
			json.NewEncoder(w).Encode(DownloadMediaResponse{
				Success: false,
				Message: fmt.Sprintf("Failed to download media: %s", errMsg),
			})
			return
		}

		// Send successful response
		json.NewEncoder(w).Encode(DownloadMediaResponse{
			Success:   true,
			Message:   fmt.Sprintf("Successfully downloaded %s media", mediaType),
			Filename:  filename,
			Path:      path,
			MediaType: mediaType,
		})
	})

	// Handler for archiving/unarchiving chats
	http.HandleFunc("/api/archive", func(w http.ResponseWriter, r *http.Request) {
		if r.Method != http.MethodPost {
			http.Error(w, "Method not allowed", http.StatusMethodNotAllowed)
			return
		}

		var req ArchiveRequest
		if err := json.NewDecoder(r.Body).Decode(&req); err != nil {
			http.Error(w, "Invalid request format", http.StatusBadRequest)
			return
		}

		if req.ChatJID == "" {
			w.Header().Set("Content-Type", "application/json")
			w.WriteHeader(http.StatusBadRequest)
			json.NewEncoder(w).Encode(SendMessageResponse{Success: false, Message: "chat_jid is required"})
			return
		}

		w.Header().Set("Content-Type", "application/json")

		// Parse the JID
		targetJID, err := types.ParseJID(req.ChatJID)
		if err != nil {
			w.WriteHeader(http.StatusBadRequest)
			json.NewEncoder(w).Encode(SendMessageResponse{Success: false, Message: fmt.Sprintf("Invalid JID: %v", err)})
			return
		}
		// For individual chats (@s.whatsapp.net), convert to LID format for app state
		if targetJID.Server == types.DefaultUserServer {
			lidJID, lidErr := client.Store.LIDs.GetLIDForPN(context.Background(), targetJID)
			if lidErr != nil || lidJID.IsEmpty() {
				w.WriteHeader(http.StatusInternalServerError)
				json.NewEncoder(w).Encode(SendMessageResponse{Success: false, Message: fmt.Sprintf("Could not find LID for %s: %v", targetJID, lidErr)})
				return
			}
			targetJID = lidJID
		}
		// Block mutation if app state recovery is in progress
		pendingRecoveryMu.Lock()
		recovering := pendingRecovery[appstate.WAPatchRegularLow]
		pendingRecoveryMu.Unlock()
		if recovering {
			w.WriteHeader(http.StatusServiceUnavailable)
			json.NewEncoder(w).Encode(SendMessageResponse{Success: false, Message: "App state recovery in progress, please retry later"})
			return
		}

		var msgKey *waCommon.MessageKey
		var lastMsgTime time.Time
		msgID, _, msgTimestamp, msgIsFromMe, err := messageStore.GetLastMessage(req.ChatJID)
		if err == nil {
			// Use targetJID (LID-converted) so the MessageKey JID matches the patch index
			msgKey = buildMessageKey(targetJID.String(), msgID, msgIsFromMe)
			lastMsgTime = msgTimestamp
		}
		patch := appstate.BuildArchive(targetJID, req.Archive, lastMsgTime, msgKey)
		err = client.SendAppState(context.Background(), patch)
		if err != nil {
			w.WriteHeader(http.StatusInternalServerError)
			json.NewEncoder(w).Encode(SendMessageResponse{Success: false, Message: fmt.Sprintf("Failed to send archive state: %v", err)})
			return
		}

		// Update local DB
		if err := messageStore.SetChatArchived(req.ChatJID, req.Archive); err != nil {
			fmt.Printf("Warning: failed to update local archive status: %v\n", err)
		}

		action := "archived"
		if !req.Archive {
			action = "unarchived"
		}
		json.NewEncoder(w).Encode(SendMessageResponse{Success: true, Message: fmt.Sprintf("Chat %s successfully", action)})
	})

	// Handler for marking chats as read
	http.HandleFunc("/api/mark-read", func(w http.ResponseWriter, r *http.Request) {
		if r.Method != http.MethodPost {
			http.Error(w, "Method not allowed", http.StatusMethodNotAllowed)
			return
		}

		var req MarkReadRequest
		if err := json.NewDecoder(r.Body).Decode(&req); err != nil {
			http.Error(w, "Invalid request format", http.StatusBadRequest)
			return
		}

		if req.ChatJID == "" {
			w.Header().Set("Content-Type", "application/json")
			w.WriteHeader(http.StatusBadRequest)
			json.NewEncoder(w).Encode(SendMessageResponse{Success: false, Message: "chat_jid is required"})
			return
		}

		w.Header().Set("Content-Type", "application/json")

		// Parse the JID
		targetJID, err := types.ParseJID(req.ChatJID)
		if err != nil {
			w.WriteHeader(http.StatusBadRequest)
			json.NewEncoder(w).Encode(SendMessageResponse{Success: false, Message: fmt.Sprintf("Invalid JID: %v", err)})
			return
		}
		// For individual chats (@s.whatsapp.net), convert to LID format for app state
		if targetJID.Server == types.DefaultUserServer {
			lidJID, lidErr := client.Store.LIDs.GetLIDForPN(context.Background(), targetJID)
			if lidErr != nil || lidJID.IsEmpty() {
				w.WriteHeader(http.StatusInternalServerError)
				json.NewEncoder(w).Encode(SendMessageResponse{Success: false, Message: fmt.Sprintf("Could not find LID for %s: %v", targetJID, lidErr)})
				return
			}
			targetJID = lidJID
		}

		// Block mutation if app state recovery is in progress
		pendingRecoveryMu.Lock()
		recovering := pendingRecovery[appstate.WAPatchRegularLow]
		pendingRecoveryMu.Unlock()
		if recovering {
			w.WriteHeader(http.StatusServiceUnavailable)
			json.NewEncoder(w).Encode(SendMessageResponse{Success: false, Message: "App state recovery in progress, please retry later"})
			return
		}

		// Get last message for MessageKey
		var msgKey *waCommon.MessageKey
		var lastMsgTime time.Time
		msgID, _, msgTimestamp, msgIsFromMe, err := messageStore.GetLastMessage(req.ChatJID)
		if err == nil {
			// Use targetJID (LID-converted) so the MessageKey JID matches the patch index
			msgKey = buildMessageKey(targetJID.String(), msgID, msgIsFromMe)
			lastMsgTime = msgTimestamp
		}

		// Send app state patch to sync read status to other devices
		patch := appstate.BuildMarkChatAsRead(targetJID, true, lastMsgTime, msgKey)
		err = client.SendAppState(context.Background(), patch)
		if err != nil {
			w.WriteHeader(http.StatusInternalServerError)
			json.NewEncoder(w).Encode(SendMessageResponse{Success: false, Message: fmt.Sprintf("Failed to send read state: %v", err)})
			return
		}

		// Send blue-tick read receipts grouped by sender (required for group chats)
		unreadBySender, err := messageStore.GetUnreadMessagesBySender(req.ChatJID)
		if err == nil {
			for sender, msgIDs := range unreadBySender {
				senderJID, err := types.ParseJID(sender)
				if err != nil {
					continue
				}
				// Convert string IDs to types.MessageID
				typedIDs := make([]types.MessageID, len(msgIDs))
				for i, id := range msgIDs {
					typedIDs[i] = types.MessageID(id)
				}
				_ = client.MarkRead(context.Background(), typedIDs, time.Now(), targetJID, senderJID)
			}
		}

		// Update local DB
		if err := messageStore.MarkChatAsRead(req.ChatJID); err != nil {
			fmt.Printf("Warning: failed to update local read status: %v\n", err)
		}

		json.NewEncoder(w).Encode(SendMessageResponse{Success: true, Message: "Chat marked as read"})
	})

	// Diagnostic endpoint: tests app state recovery using two strategies.
	// Query params:
	//   ?collection=regular_low (default) — which app state to recover
	//   ?strategy=server (default) | phone | both
	http.HandleFunc("/api/test-recovery", func(w http.ResponseWriter, r *http.Request) {
		if r.Method != http.MethodPost {
			http.Error(w, "Method not allowed", http.StatusMethodNotAllowed)
			return
		}
		w.Header().Set("Content-Type", "application/json")

		// Parse collection name from query param
		collectionParam := r.URL.Query().Get("collection")
		if collectionParam == "" {
			collectionParam = "regular_low"
		}
		var name appstate.WAPatchName
		switch collectionParam {
		case "regular_low":
			name = appstate.WAPatchRegularLow
		case "regular_high":
			name = appstate.WAPatchRegularHigh
		case "regular":
			name = appstate.WAPatchRegular
		case "critical_block":
			name = appstate.WAPatchCriticalBlock
		case "critical_unblock_low":
			name = appstate.WAPatchCriticalUnblockLow
		default:
			json.NewEncoder(w).Encode(SendMessageResponse{Success: false, Message: fmt.Sprintf("Unknown collection: %s. Valid: regular_low, regular_high, regular, critical_block, critical_unblock_low", collectionParam)})
			return
		}

		strategy := r.URL.Query().Get("strategy")
		if strategy == "" {
			strategy = "server"
		}

		type stepResult struct {
			Step    string `json:"step"`
			Success bool   `json:"success"`
			Detail  string `json:"detail"`
		}
		var steps []stepResult

		// Strategy A: FetchAppState from WhatsApp server (no phone involvement)
		if strategy == "server" || strategy == "both" {
			fmt.Fprintf(os.Stderr, "[test-recovery] === SERVER STRATEGY for %s ===\n", name)

			// Step 1: check current version
			currentVersion, _, err := client.Store.AppState.GetAppStateVersion(context.Background(), string(name))
			fmt.Fprintf(os.Stderr, "[test-recovery] Current local version for %s: v%d (err=%v)\n", name, currentVersion, err)
			steps = append(steps, stepResult{"server_current_version", err == nil, fmt.Sprintf("v%d", currentVersion)})

			// Step 2: delete local version to force full re-sync
			fmt.Fprintf(os.Stderr, "[test-recovery] Deleting local app state version for %s...\n", name)
			if err := client.Store.AppState.DeleteAppStateVersion(context.Background(), string(name)); err != nil {
				steps = append(steps, stepResult{"server_delete_version", false, err.Error()})
			} else {
				steps = append(steps, stepResult{"server_delete_version", true, "OK"})
			}

			// Step 3: FetchAppState with fullSync=true
			fmt.Fprintf(os.Stderr, "[test-recovery] FetchAppState(%s, fullSync=true)...\n", name)
			if err := client.FetchAppState(context.Background(), name, true, false); err != nil {
				errMsg := fmt.Sprintf("FetchAppState failed: %v", err)
				fmt.Fprintf(os.Stderr, "[test-recovery] %s\n", errMsg)
				steps = append(steps, stepResult{"server_fetch", false, errMsg})
			} else {
				newVersion, _, _ := client.Store.AppState.GetAppStateVersion(context.Background(), string(name))
				result := fmt.Sprintf("OK — now at v%d", newVersion)
				fmt.Fprintf(os.Stderr, "[test-recovery] %s\n", result)
				steps = append(steps, stepResult{"server_fetch", true, result})
			}
		}

		// Strategy B: ask the phone directly via peer message
		if strategy == "phone" || strategy == "both" {
			fmt.Fprintf(os.Stderr, "[test-recovery] === PHONE STRATEGY for %s ===\n", name)

			// Drain any stale signals
			for {
				select {
				case <-recoveryDone:
				default:
					goto drained
				}
			}
		drained:

			// Step 1: delete local app state version
			fmt.Fprintf(os.Stderr, "[test-recovery] Deleting local app state version for %s...\n", name)
			if err := client.Store.AppState.DeleteAppStateVersion(context.Background(), string(name)); err != nil {
				steps = append(steps, stepResult{"phone_delete_version", false, err.Error()})
			} else {
				steps = append(steps, stepResult{"phone_delete_version", true, "OK"})
			}

			// Step 2: build and send recovery request
			fmt.Fprintf(os.Stderr, "[test-recovery] Sending peer recovery request for %s...\n", name)
			msg := whatsmeow.BuildAppStateRecoveryRequest(name)
			_, err := client.SendPeerMessage(context.Background(), msg)
			if err != nil {
				steps = append(steps, stepResult{"phone_send", false, err.Error()})
			} else {
				steps = append(steps, stepResult{"phone_send", true, "OK — peer message sent"})

				// Step 3: wait for phone response
				fmt.Fprintf(os.Stderr, "[test-recovery] Waiting up to 30s for phone response...\n")
				select {
				case recovered := <-recoveryDone:
					result := fmt.Sprintf("Phone responded with recovery for %s", recovered)
					fmt.Fprintf(os.Stderr, "[test-recovery] %s\n", result)
					steps = append(steps, stepResult{"phone_wait", true, result})
				case <-time.After(120 * time.Second):
					fmt.Fprintf(os.Stderr, "[test-recovery] TIMEOUT — no phone response\n")
					steps = append(steps, stepResult{"phone_wait", false, "TIMEOUT — no response from phone within 120s"})
				}
			}
		}

		// Return structured results
		allOK := true
		for _, s := range steps {
			if !s.Success {
				allOK = false
				break
			}
		}
		result := map[string]interface{}{
			"success":    allOK,
			"collection": string(name),
			"strategy":   strategy,
			"steps":      steps,
		}
		if !allOK {
			w.WriteHeader(http.StatusInternalServerError)
		}
		json.NewEncoder(w).Encode(result)
	})

	// Nuclear option: sends APP_STATE_FATAL_EXCEPTION_NOTIFICATION to the phone,
	// which resets the app state collections on the server. ALL linked devices will
	// be logged out. After this, delete DBs, restart, and re-scan QR.
	http.HandleFunc("/api/nuke-appstate", func(w http.ResponseWriter, r *http.Request) {
		if r.Method != http.MethodPost {
			http.Error(w, "Method not allowed", http.StatusMethodNotAllowed)
			return
		}
		w.Header().Set("Content-Type", "application/json")
		fmt.Fprintf(os.Stderr, "[nuke-appstate] Building fatal exception notification for regular_low...\n")
		msg := whatsmeow.BuildFatalAppStateExceptionNotification(appstate.WAPatchRegularLow)
		fmt.Fprintf(os.Stderr, "[nuke-appstate] Sending to phone...\n")
		_, err := client.SendPeerMessage(context.Background(), msg)
		if err != nil {
			errMsg := fmt.Sprintf("Failed to send fatal exception notification: %v", err)
			fmt.Fprintf(os.Stderr, "[nuke-appstate] %s\n", errMsg)
			w.WriteHeader(http.StatusInternalServerError)
			json.NewEncoder(w).Encode(SendMessageResponse{Success: false, Message: errMsg})
			return
		}
		fmt.Fprintf(os.Stderr, "[nuke-appstate] Sent. All linked devices will be logged out.\n")
		json.NewEncoder(w).Encode(SendMessageResponse{
			Success: true,
			Message: "Fatal exception notification sent. All linked devices will be logged out. Delete DBs, restart bridge, and re-scan QR code.",
		})
	})

	// Start the server
	serverAddr := fmt.Sprintf(":%d", port)
	fmt.Printf("Starting REST API server on %s...\n", serverAddr)

	// Run server in a goroutine so it doesn't block
	go func() {
		if err := http.ListenAndServe(serverAddr, nil); err != nil {
			fmt.Printf("REST API server error: %v\n", err)
		}
	}()
}

// loadEnv reads a .env file and sets environment variables (does not override existing ones).
func loadEnv(path string) {
	f, err := os.Open(path)
	if err != nil {
		return
	}
	defer f.Close()
	scanner := bufio.NewScanner(f)
	for scanner.Scan() {
		line := strings.TrimSpace(scanner.Text())
		if line == "" || strings.HasPrefix(line, "#") {
			continue
		}
		key, val, ok := strings.Cut(line, "=")
		if !ok {
			continue
		}
		key = strings.TrimSpace(key)
		val = strings.TrimSpace(val)
		if os.Getenv(key) == "" {
			os.Setenv(key, val)
		}
	}
}

var httpAlertClient = &http.Client{Timeout: 10 * time.Second}

// sendLogAlert sends a fire-and-forget HTTP POST with the log level and message.
func sendLogAlert(level, message, logsURL, bearerToken string) {
	if logsURL == "" || bearerToken == "" {
		return
	}
	go func() {
		payload, _ := json.Marshal(map[string]string{
			"level":   level,
			"message": message,
		})
		req, err := http.NewRequest("POST", logsURL, bytes.NewReader(payload))
		if err != nil {
			return
		}
		req.Header.Set("Content-Type", "application/json")
		req.Header.Set("Authorization", "Bearer "+bearerToken)
		resp, err := httpAlertClient.Do(req)
		if err != nil {
			return
		}
		resp.Body.Close()
	}()
}

// alertLogger wraps a waLog.Logger to also send WARN/ERROR logs via HTTP.
type alertLogger struct {
	waLog.Logger
	logsURL     string
	bearerToken string
}

func (l *alertLogger) Warnf(msg string, args ...interface{}) {
	l.Logger.Warnf(msg, args...)
	sendLogAlert("warning", fmt.Sprintf(msg, args...), l.logsURL, l.bearerToken)
}

func (l *alertLogger) Errorf(msg string, args ...interface{}) {
	l.Logger.Errorf(msg, args...)
	sendLogAlert("error", fmt.Sprintf(msg, args...), l.logsURL, l.bearerToken)
}

func (l *alertLogger) Sub(module string) waLog.Logger {
	return &alertLogger{
		Logger:      l.Logger.Sub(module),
		logsURL:     l.logsURL,
		bearerToken: l.bearerToken,
	}
}

func main() {
	// Load .env file (next to executable)
	loadEnv(".env")

	logsURL := os.Getenv("LOGS_URL")
	bearerToken := os.Getenv("LOGS_BEARER_TOKEN")

	// Set up logger (with optional HTTP alerting for WARN/ERROR)
	baseLogger := waLog.Stdout("Client", "INFO", true)
	logger := waLog.Logger(&alertLogger{Logger: baseLogger, logsURL: logsURL, bearerToken: bearerToken})
	logger.Infof("Starting WhatsApp client...")

	// Create database connection for storing session data
	dbLog := waLog.Logger(&alertLogger{Logger: waLog.Stdout("Database", "INFO", true), logsURL: logsURL, bearerToken: bearerToken})

	// Create directory for database if it doesn't exist
	if err := os.MkdirAll("store", 0755); err != nil {
		logger.Errorf("Failed to create store directory: %v", err)
		return
	}

	container, err := sqlstore.New(context.Background(), "sqlite3", "file:store/whatsapp.db?_foreign_keys=on", dbLog)
	if err != nil {
		logger.Errorf("Failed to connect to database: %v", err)
		return
	}

	// Get device store - This contains session information
	deviceStore, err := container.GetFirstDevice(context.Background())
	if err != nil {
		if err == sql.ErrNoRows {
			// No device exists, create one
			deviceStore = container.NewDevice()
			logger.Infof("Created new device")
		} else {
			logger.Errorf("Failed to get device: %v", err)
			return
		}
	}

	// Create client instance
	client := whatsmeow.NewClient(deviceStore, logger)
	if client == nil {
		logger.Errorf("Failed to create WhatsApp client")
		return
	}
	// Emit Archive/Pin/Mute events during full app state syncs so our handler
	// can update messages.db. Without this, FetchAppState(fullSync=true) silently
	// skips event dispatch and our DB never learns the correct archive status.
	client.EmitAppStateEventsOnFullSync = true

	// Initialize message store
	messageStore, err := NewMessageStore()
	if err != nil {
		logger.Errorf("Failed to initialize message store: %v", err)
		return
	}
	defer messageStore.Close()

	// Initialize sync debug log
	syncDebugFile := initSyncDebugLog()
	if syncDebugFile != nil {
		defer syncDebugFile.Close()
	}

	// Wire up LID store so NormalizeJID can resolve PN → LID
	messageStore.SetLIDStore(client.Store.LIDs)

	// resolveJID normalizes a JID to the canonical form (LID for individuals).
	resolveJID := func(jid types.JID) string {
		return messageStore.NormalizeJID(jid)
	}

	// attemptRecovery tries to fix a broken app state patch chain.
	// Step 1: full re-sync from the WhatsApp server (requests a snapshot).
	// Step 2 (fallback): ask the phone for an unencrypted recovery copy.
	attemptRecovery := func(name appstate.WAPatchName) {
		logger.Infof("Attempting full re-sync of %s from server...", name)
		if err := client.FetchAppState(context.Background(), name, true, false); err != nil {
			logger.Warnf("Full re-sync of %s failed: %v — falling back to phone recovery request", name, err)
			if err := client.Store.AppState.DeleteAppStateVersion(context.Background(), string(name)); err != nil {
				logger.Warnf("Failed to clear app state version for %s: %v", name, err)
			}
			time.Sleep(3 * time.Second)
			msg := whatsmeow.BuildAppStateRecoveryRequest(name)
			_, err := client.SendPeerMessage(context.Background(), msg)
			if err != nil {
				logger.Warnf("Recovery request to phone failed for %s: %v", name, err)
			} else {
				logger.Infof("Recovery request sent to phone for %s, waiting for response...", name)
			}
		} else {
			logger.Infof("Full re-sync of %s from server succeeded", name)
		}
	}

	// Setup event handling for messages and history sync
	client.AddEventHandler(func(evt interface{}) {
		switch v := evt.(type) {
		case *events.Message:
			// Debug: log any protocol messages (recovery responses come back this way)
			if protoMsg := v.Message.GetProtocolMessage(); protoMsg != nil {
				logger.Infof("[PROTO] Received ProtocolMessage type=%v from %s", protoMsg.GetType(), v.Info.Sender.String())
			}
			// Process regular messages
			handleMessage(client, messageStore, v, logger)

		case *events.HistorySync:
			// Process history sync events
			handleHistorySync(client, messageStore, v, logger)

		case *events.Archive:
			rawJID := v.JID.String()
			chatJID := resolveJID(v.JID)
			archived := v.Action.GetArchived()
			actionTS := v.Timestamp
			fmt.Printf("[APP_STATE] Archive event: %s archived=%v\n", chatJID, archived)
			atomic.AddInt64(&totalAppStateArchive, 1)
			if archived {
				atomic.AddInt64(&totalAppStateArchiveTrue, 1)
			} else {
				atomic.AddInt64(&totalAppStateArchiveFalse, 1)
			}
			if syncLog != nil {
				resolveStatus := "SAME"
				if chatJID != rawJID {
					resolveStatus = "RESOLVED"
				} else if v.JID.Server == "s.whatsapp.net" {
					resolveStatus = "LID_FAIL"
				} else if v.JID.Server == "lid" {
					resolveStatus = "LID_NATIVE"
				}
				syncLog.Printf("[APPSTATE] Archive: raw=%s resolved=%s (%s) archived=%v ts=%s (totals: true=%d false=%d)",
					rawJID, chatJID, resolveStatus, archived, actionTS.Format(time.RFC3339),
					atomic.LoadInt64(&totalAppStateArchiveTrue), atomic.LoadInt64(&totalAppStateArchiveFalse))
			}
			err := messageStore.SetChatArchived(chatJID, archived)
			if err != nil {
				logger.Warnf("Failed to update archive status for %s: %v", chatJID, err)
			}

		case *events.Pin:
			rawJID := v.JID.String()
			chatJID := resolveJID(v.JID)
			pinned := v.Action.GetPinned()
			fmt.Printf("[APP_STATE] Pin event: %s pinned=%v\n", chatJID, pinned)
			if syncLog != nil {
				syncLog.Printf("[APPSTATE] Pin: raw=%s resolved=%s pinned=%v", rawJID, chatJID, pinned)
			}
			err := messageStore.SetChatPinned(chatJID, pinned)
			if err != nil {
				logger.Warnf("Failed to update pin status for %s: %v", chatJID, err)
			}

		case *events.Mute:
			rawJID := v.JID.String()
			chatJID := resolveJID(v.JID)
			muteEnd := v.Action.GetMuteEndTimestamp()
			fmt.Printf("[APP_STATE] Mute event: %s muteEnd=%v\n", chatJID, muteEnd)
			if syncLog != nil {
				syncLog.Printf("[APPSTATE] Mute: raw=%s resolved=%s muteEnd=%v", rawJID, chatJID, muteEnd)
			}
			err := messageStore.SetChatMuted(chatJID, muteEnd)
			if err != nil {
				logger.Warnf("Failed to update mute status for %s: %v", chatJID, err)
			}

		case *events.MarkChatAsRead:
			chatJID := resolveJID(v.JID)
			isRead := v.Action.GetRead()
			if isRead {
				err := messageStore.MarkChatAsRead(chatJID)
				if err != nil {
					logger.Warnf("Failed to mark chat %s as read: %v", chatJID, err)
				}
			} else {
				err := messageStore.MarkChatAsUnread(chatJID)
				if err != nil {
					logger.Warnf("Failed to mark chat %s as unread: %v", chatJID, err)
				}
			}
			logger.Infof("Chat %s read status: %v", chatJID, isRead)

		case *events.Receipt:
			if v.Type == types.ReceiptTypeRead || v.Type == types.ReceiptTypeReadSelf {
				chatJID := messageStore.NormalizeJID(v.Chat)
				err := messageStore.MarkMessagesAsRead(chatJID, v.MessageIDs)
				if err != nil {
					logger.Warnf("Failed to mark messages as read in %s: %v", chatJID, err)
				} else {
					logger.Infof("Marked %d messages as read in %s (type: %s)", len(v.MessageIDs), chatJID, v.Type)
				}
			}

		case *events.Connected:
			logger.Infof("Connected to WhatsApp")
			// Re-wire LID store now that connection is established and device is registered.
			// On fresh pairings, client.Store.LIDs is nil before QR scan completes.
			if client.Store.LIDs != nil {
				messageStore.SetLIDStore(client.Store.LIDs)
				if syncLog != nil {
					syncLog.Println("[STARTUP] LID store wired after Connected event")
				}
			} else if syncLog != nil {
				syncLog.Println("[STARTUP] WARNING: client.Store.LIDs still nil after Connected event")
			}
			pendingRecoveryMu.Lock()
			pending := make([]appstate.WAPatchName, 0, len(pendingRecovery))
			for name := range pendingRecovery {
				pending = append(pending, name)
			}
			pendingRecoveryMu.Unlock()
			if len(pending) > 0 {
				logger.Infof("Retrying recovery for %d app state(s) after reconnect: %v", len(pending), pending)
				go func(names []appstate.WAPatchName) {
					// Wait for signal sessions to be fully established
					time.Sleep(5 * time.Second)
					for _, name := range names {
						attemptRecovery(name)
					}
				}(pending)
			}

		case *events.AppStateSyncError:
			// When app state sync fails (e.g. corrupted LTHash in the patch chain),
			// try a full re-sync from the server, then fall back to phone recovery.
			logger.Warnf("App state sync failed for %s: %v", v.Name, v.Error)
			pendingRecoveryMu.Lock()
			alreadyRecovering := pendingRecovery[v.Name]
			if !alreadyRecovering {
				pendingRecovery[v.Name] = true
			}
			pendingRecoveryMu.Unlock()
			if alreadyRecovering {
				// Recovery already in progress (e.g. FetchAppState retry also failed)
				logger.Warnf("Recovery already in progress for %s, skipping duplicate", v.Name)
				break
			}
			go func(name appstate.WAPatchName) {
				attemptRecovery(name)
			}(v.Name)

		case *events.Contact:
			// Contact name updated from app state sync (address book entry changed)
			chatJID := resolveJID(v.JID)
			fullName := v.Action.GetFullName()
			firstName := v.Action.GetFirstName()
			name := fullName
			if name == "" {
				name = firstName
			}
			if name != "" {
				if err := messageStore.UpdateChatName(chatJID, name); err != nil {
					logger.Warnf("Failed to update contact name for %s: %v", chatJID, err)
				} else {
					logger.Infof("Contact name updated: %s -> %s", chatJID, name)
				}
			}

		case *events.PushName:
			// Push name received from an incoming message
			chatJID := resolveJID(v.JID)
			if v.NewPushName != "" {
				if err := messageStore.UpdateChatName(chatJID, v.NewPushName); err != nil {
					logger.Warnf("Failed to update push name for %s: %v", chatJID, err)
				} else {
					logger.Infof("Push name updated: %s -> %s (was %q)", chatJID, v.NewPushName, v.OldPushName)
				}
			}

		case *events.BusinessName:
			// Business name received (verified business accounts)
			chatJID := resolveJID(v.JID)
			if v.NewBusinessName != "" {
				if err := messageStore.UpdateChatName(chatJID, v.NewBusinessName); err != nil {
					logger.Warnf("Failed to update business name for %s: %v", chatJID, err)
				} else {
					logger.Infof("Business name updated: %s -> %s (was %q)", chatJID, v.NewBusinessName, v.OldBusinessName)
				}
			}

		case *events.AppStateSyncComplete:
			fmt.Fprintf(os.Stderr, "[APP_STATE_SYNC] %s synced to v%d (recovery=%v)\n", v.Name, v.Version, v.Recovery)
			logger.Infof("App state %s synced to v%d (recovery=%v)", v.Name, v.Version, v.Recovery)
			pendingRecoveryMu.Lock()
			delete(pendingRecovery, v.Name)
			pendingRecoveryMu.Unlock()
			if v.Recovery {
				select {
				case recoveryDone <- v.Name:
				default:
				}
			}
			// After contacts app state finishes, backfill any chats still named as phone numbers
			go backfillContactNames(client, messageStore, logger)

		case *events.LoggedOut:
			logger.Warnf("Device logged out, please scan QR code to log in again")
		}
	})

	// Set device name and icon shown under "Linked Devices" on phone.
	// Customize via WHATSAPP_DEVICE_NAME env var (default: "Koba CoS").
	deviceName := os.Getenv("WHATSAPP_DEVICE_NAME")
	if deviceName == "" {
		deviceName = "Koba CoS"
	}
	store.DeviceProps.Os = proto.String(deviceName)
	store.DeviceProps.PlatformType = waCompanionReg.DeviceProps_DESKTOP.Enum()

	// Create channel to track connection success
	connected := make(chan bool, 1)

	// Connect to WhatsApp
	if client.Store.ID == nil {
		// No ID stored, this is a new client, need to pair with phone
		qrChan, _ := client.GetQRChannel(context.Background())
		err = client.Connect()
		if err != nil {
			logger.Errorf("Failed to connect: %v", err)
			return
		}

		// Print QR code for pairing with phone
		for evt := range qrChan {
			if evt.Event == "code" {
				fmt.Println("\nScan this QR code with your WhatsApp app:")
				qrterminal.GenerateHalfBlock(evt.Code, qrterminal.L, os.Stdout)
			} else if evt.Event == "success" {
				connected <- true
				break
			}
		}

		// Wait for connection
		select {
		case <-connected:
			fmt.Println("\nSuccessfully connected and authenticated!")
		case <-time.After(3 * time.Minute):
			logger.Errorf("Timeout waiting for QR code scan")
			return
		}
	} else {
		// Already logged in, connect with exponential backoff retry.
		// This handles cases where the bridge starts before the network is ready
		// (e.g. auto-start on login before WiFi connects).
		maxRetries := 6
		backoff := 2 * time.Second
		for attempt := 1; attempt <= maxRetries; attempt++ {
			err = client.Connect()
			if err == nil {
				break
			}
			if attempt == maxRetries {
				logger.Errorf("Failed to connect after %d attempts: %v", maxRetries, err)
				return
			}
			logger.Warnf("Connection attempt %d/%d failed: %v — retrying in %v", attempt, maxRetries, err, backoff)
			time.Sleep(backoff)
			backoff *= 2
		}
		connected <- true
	}

	// Wait a moment for connection to stabilize
	time.Sleep(2 * time.Second)

	if !client.IsConnected() {
		logger.Errorf("Failed to establish stable connection")
		return
	}

	fmt.Println("\n✓ Connected to WhatsApp! Type 'help' for commands.")

	// Reconcile PN/LID duplicate rows once the LID store has populated.
	go func() {
		// --- COMMENTED OUT: forced app state resync (Experiment #3) ---
		// Was a defensive guard against one-time LTHash corruption.
		// Removed to simplify startup — natural app state events are sufficient.
		//
		// time.Sleep(10 * time.Second)
		// if syncLog != nil {
		// 	syncLog.Println("[STARTUP] Beginning app state resync...")
		// }
		// logger.Infof("Performing startup resync of regular_low app state...")
		// if err := client.Store.AppState.DeleteAppStateVersion(context.Background(), string(appstate.WAPatchRegularLow)); err != nil {
		// 	logger.Warnf("Failed to clear regular_low app state version on startup: %v", err)
		// }
		// if err := client.FetchAppState(context.Background(), appstate.WAPatchRegularLow, true, false); err != nil {
		// 	logger.Warnf("Startup resync of regular_low failed: %v (will recover on demand)", err)
		// } else {
		// 	logger.Infof("Startup resync of regular_low succeeded")
		// }
		// if syncLog != nil {
		// 	syncLog.Printf("[STARTUP] App state resync done. Archive totals: true=%d false=%d",
		// 		atomic.LoadInt64(&totalAppStateArchiveTrue), atomic.LoadInt64(&totalAppStateArchiveFalse))
		// }
		// --- END COMMENTED OUT ---

		// Wait for events to settle, then reconcile JID rows
		time.Sleep(15 * time.Second) // combined wait (was 10s + 5s)
		reconcileJIDRows(messageStore, logger)
	}()

	// Start REST API server
	startRESTServer(client, messageStore, 8080)

	// Create a channel to keep the main goroutine alive
	exitChan := make(chan os.Signal, 1)
	signal.Notify(exitChan, syscall.SIGINT, syscall.SIGTERM)

	fmt.Println("REST server is running. Press Ctrl+C to disconnect and exit.")

	// Wait for termination signal
	<-exitChan

	fmt.Println("Disconnecting...")
	// Disconnect client
	client.Disconnect()
}

// isPhoneNumber returns true if s consists entirely of digits (a phone-number placeholder).
func isPhoneNumber(s string) bool {
	if len(s) == 0 {
		return false
	}
	for _, c := range s {
		if c < '0' || c > '9' {
			return false
		}
	}
	return true
}

// GetChatName determines the appropriate name for a chat based on JID and other info
func GetChatName(client *whatsmeow.Client, messageStore *MessageStore, jid types.JID, chatJID string, conversation interface{}, sender string, logger waLog.Logger) string {
	// First, check if chat already exists in database with a real (non-phone-number) name
	var existingName string
	err := messageStore.db.QueryRow("SELECT name FROM chats WHERE jid = ?", chatJID).Scan(&existingName)
	if err == nil && existingName != "" && !isPhoneNumber(existingName) {
		// Chat exists with a real name, use that
		logger.Infof("Using existing chat name for %s: %s", chatJID, existingName)
		return existingName
	}

	// Need to determine chat name
	var name string

	if jid.Server == "g.us" {
		// This is a group chat
		logger.Infof("Getting name for group: %s", chatJID)

		// Use conversation data if provided (from history sync)
		if conversation != nil {
			// Extract name from conversation if available
			// This uses type assertions to handle different possible types
			var displayName, convName *string
			// Try to extract the fields we care about regardless of the exact type
			v := reflect.ValueOf(conversation)
			if v.Kind() == reflect.Ptr && !v.IsNil() {
				v = v.Elem()

				// Try to find DisplayName field
				if displayNameField := v.FieldByName("DisplayName"); displayNameField.IsValid() && displayNameField.Kind() == reflect.Ptr && !displayNameField.IsNil() {
					dn := displayNameField.Elem().String()
					displayName = &dn
				}

				// Try to find Name field
				if nameField := v.FieldByName("Name"); nameField.IsValid() && nameField.Kind() == reflect.Ptr && !nameField.IsNil() {
					n := nameField.Elem().String()
					convName = &n
				}
			}

			// Use the name we found
			if displayName != nil && *displayName != "" {
				name = *displayName
			} else if convName != nil && *convName != "" {
				name = *convName
			}
		}

		// If we didn't get a name, try group info
		if name == "" {
			groupInfo, err := client.GetGroupInfo(context.Background(), jid)
			if err == nil && groupInfo.Name != "" {
				name = groupInfo.Name
			} else {
				// Fallback name for groups
				name = fmt.Sprintf("Group %s", jid.User)
			}
		}

		logger.Infof("Using group name: %s", name)
	} else {
		// This is an individual contact
		logger.Infof("Getting name for contact: %s", chatJID)

		// Try contact store — check FullName, PushName, BusinessName in order
		contact, err := client.Store.Contacts.GetContact(context.Background(), jid)
		if err == nil {
			if contact.FullName != "" {
				name = contact.FullName
			} else if contact.PushName != "" {
				name = contact.PushName
			} else if contact.BusinessName != "" {
				name = contact.BusinessName
			}
		}

		// Fallbacks
		if name == "" && sender != "" {
			name = sender
		}
		if name == "" {
			name = jid.User
		}

		logger.Infof("Using contact name: %s", name)
	}

	return name
}

// Handle history sync events
func handleHistorySync(client *whatsmeow.Client, messageStore *MessageStore, historySync *events.HistorySync, logger waLog.Logger) {
	syncType := historySync.Data.GetSyncType()
	numConvs := len(historySync.Data.Conversations)
	fmt.Printf("Received history sync event: type=%s, conversations=%d\n", syncType, numConvs)
	if syncLog != nil {
		syncLog.Printf("[HSYNC] Event: type=%s conversations=%d", syncType, numConvs)
	}

	// Per-event counters
	eventStored := 0
	eventSkippedEmpty := 0
	eventSkippedNil := 0
	eventConvs := 0

	for _, conversation := range historySync.Data.Conversations {
		// Parse JID from the conversation
		if conversation.ID == nil {
			continue
		}

		rawJID := *conversation.ID

		// Try to parse the JID
		jid, err := types.ParseJID(rawJID)
		if err != nil {
			logger.Warnf("Failed to parse JID %s: %v", rawJID, err)
			continue
		}

		// Normalize to LID for individual chats
		chatJID := messageStore.NormalizeJID(jid)
		jidResolved := "SAME"
		if chatJID != rawJID {
			jidResolved = "LID_OK"
		} else if jid.Server == "s.whatsapp.net" {
			jidResolved = "LID_FAIL"
		}

		// Get appropriate chat name by passing the history sync conversation directly
		name := GetChatName(client, messageStore, jid, chatJID, conversation, "", logger)

		// Read chat metadata from the Conversation proto
		unreadCount := conversation.GetUnreadCount()
		chatUnreadCount := int(unreadCount)
		if conversation.GetMarkedAsUnread() {
			chatUnreadCount = -1 // -1 signals "explicitly marked unread"
		}
		pinned := conversation.GetPinned() > 0
		muteEndTime := int64(conversation.GetMuteEndTime())

		// Process messages
		messages := conversation.Messages
		convMsgsRaw := len(messages)
		convStored := 0
		convSkippedEmpty := 0
		convSkippedNil := 0

		if len(messages) > 0 {
			// Update chat with latest message timestamp
			latestMsg := messages[0]
			if latestMsg == nil || latestMsg.Message == nil {
				convSkippedNil++
				if syncLog != nil {
					syncLog.Printf("[HSYNC]   Conv: %s → %s (%s) msgs_raw=%d SKIPPED (nil latestMsg)", rawJID, chatJID, jidResolved, convMsgsRaw)
				}
				continue
			}

			// Get timestamp from message info
			timestamp := time.Time{}
			if ts := latestMsg.Message.GetMessageTimestamp(); ts != 0 {
				timestamp = time.Unix(int64(ts), 0)
			} else {
				convSkippedNil++
				if syncLog != nil {
					syncLog.Printf("[HSYNC]   Conv: %s → %s (%s) msgs_raw=%d SKIPPED (no timestamp)", rawJID, chatJID, jidResolved, convMsgsRaw)
				}
				continue
			}

			messageStore.StoreChatFromHistory(chatJID, name, timestamp, conversation.GetArchived(), pinned, muteEndTime, chatUnreadCount)

			// Count incoming messages to determine which are unread.
			// Messages are ordered newest-first; the last `unreadCount` incoming
			// messages should be marked as unread.
			incomingCount := 0
			for _, msg := range messages {
				if msg == nil || msg.Message == nil || msg.Message.Key == nil {
					continue
				}
				fromMe := msg.Message.Key.FromMe != nil && *msg.Message.Key.FromMe
				if !fromMe {
					incomingCount++
				}
			}

			// Track how many incoming messages we've seen (newest first)
			incomingSeen := 0

			// Store messages
			for _, msg := range messages {
				if msg == nil || msg.Message == nil {
					convSkippedNil++
					continue
				}

				// Extract text content
				var content string
				if msg.Message.Message != nil {
					if conv := msg.Message.Message.GetConversation(); conv != "" {
						content = conv
					} else if ext := msg.Message.Message.GetExtendedTextMessage(); ext != nil {
						content = ext.GetText()
					}
				}

				// Extract media info
				var mediaType, filename, url string
				var mediaKey, fileSHA256, fileEncSHA256 []byte
				var fileLength uint64

				if msg.Message.Message != nil {
					mediaType, filename, url, mediaKey, fileSHA256, fileEncSHA256, fileLength = extractMediaInfo(msg.Message.Message)
				}

				// Skip messages with no content and no media
				if content == "" && mediaType == "" {
					convSkippedEmpty++
					continue
				}

				// Determine sender
				var sender string
				isFromMe := false
				if msg.Message.Key != nil {
					if msg.Message.Key.FromMe != nil {
						isFromMe = *msg.Message.Key.FromMe
					}
					if !isFromMe && msg.Message.Key.Participant != nil && *msg.Message.Key.Participant != "" {
						sender = *msg.Message.Key.Participant
					} else if isFromMe {
						sender = client.Store.ID.User
					} else {
						sender = jid.User
					}
				} else {
					sender = jid.User
				}

				// Store message
				msgID := ""
				if msg.Message.Key != nil && msg.Message.Key.ID != nil {
					msgID = *msg.Message.Key.ID
				}

				// Get message timestamp
				timestamp := time.Time{}
				if ts := msg.Message.GetMessageTimestamp(); ts != 0 {
					timestamp = time.Unix(int64(ts), 0)
				} else {
					convSkippedNil++
					continue
				}

				// Determine read status: the newest `unreadCount` incoming messages
				// are unread, everything else is read. Messages from me are always read.
				isRead := true
				if !isFromMe {
					incomingSeen++
					if incomingSeen <= int(unreadCount) {
						isRead = false
					}
				}

				err = messageStore.StoreHistoryMessage(
					msgID,
					chatJID,
					sender,
					content,
					timestamp,
					isFromMe,
					mediaType,
					filename,
					url,
					mediaKey,
					fileSHA256,
					fileEncSHA256,
					fileLength,
					isRead,
				)
				if err != nil {
					logger.Warnf("Failed to store history message: %v", err)
				} else {
					convStored++
				}
			}
		}

		eventStored += convStored
		eventSkippedEmpty += convSkippedEmpty
		eventSkippedNil += convSkippedNil
		eventConvs++

		if syncLog != nil {
			syncLog.Printf("[HSYNC]   Conv: %s → %s (%s) archived=%v pinned=%v muteEnd=%d unread=%d markedUnread=%v msgs_raw=%d stored=%d skipped_empty=%d skipped_nil=%d",
				rawJID, chatJID, jidResolved, conversation.GetArchived(), pinned, muteEndTime, unreadCount, conversation.GetMarkedAsUnread(), convMsgsRaw, convStored, convSkippedEmpty, convSkippedNil)
		}
	}

	// Update running totals
	atomic.AddInt64(&totalHSyncEvents, 1)
	atomic.AddInt64(&totalHSyncConvs, int64(eventConvs))
	atomic.AddInt64(&totalHSyncMsgsStored, int64(eventStored))
	atomic.AddInt64(&totalHSyncMsgsSkipped, int64(eventSkippedEmpty+eventSkippedNil))

	fmt.Printf("History sync complete. Stored %d messages.\n", eventStored)
	if syncLog != nil {
		syncLog.Printf("[HSYNC] Event complete: type=%s convs=%d stored=%d skipped_empty=%d skipped_nil=%d",
			syncType, eventConvs, eventStored, eventSkippedEmpty, eventSkippedNil)
		syncLog.Printf("[HSYNC] Running totals: events=%d convs=%d msgs_stored=%d msgs_skipped=%d jid_ok=%d jid_fail=%d",
			atomic.LoadInt64(&totalHSyncEvents), atomic.LoadInt64(&totalHSyncConvs),
			atomic.LoadInt64(&totalHSyncMsgsStored), atomic.LoadInt64(&totalHSyncMsgsSkipped),
			atomic.LoadInt64(&totalJIDResolveOK), atomic.LoadInt64(&totalJIDResolveFail))
	}
}

// reconcileJIDRows fixes the JID format split where history sync stored chats
// under @s.whatsapp.net (PN) and app state events created duplicate rows under
// @lid. It merges metadata from LID rows into PN rows, migrates messages, and
// renames to canonical LID format.
func reconcileJIDRows(messageStore *MessageStore, logger waLog.Logger) {
	if syncLog != nil {
		syncLog.Println("[RECONCILE] Starting JID reconciliation pass...")
	}

	if messageStore.lidStore == nil {
		if syncLog != nil {
			syncLog.Println("[RECONCILE] No LID store available, skipping")
		}
		return
	}

	// Find all individual chat rows stored under PN format
	rows, err := messageStore.db.Query(
		`SELECT jid, name, is_archived, is_pinned, mute_end_time FROM chats WHERE jid LIKE '%@s.whatsapp.net'`)
	if err != nil {
		if syncLog != nil {
			syncLog.Printf("[RECONCILE] Query failed: %v", err)
		}
		return
	}

	type pnRow struct {
		jid        string
		name       string
		isArchived bool
		isPinned   bool
		muteEnd    int64
	}
	var pnRows []pnRow
	for rows.Next() {
		var r pnRow
		if err := rows.Scan(&r.jid, &r.name, &r.isArchived, &r.isPinned, &r.muteEnd); err != nil {
			continue
		}
		pnRows = append(pnRows, r)
	}
	rows.Close()

	merged := 0
	renamed := 0
	skipped := 0

	for _, pn := range pnRows {
		// Parse back to types.JID to look up LID
		pnJID, err := types.ParseJID(pn.jid)
		if err != nil {
			skipped++
			continue
		}

		lidJID, err := messageStore.lidStore.GetLIDForPN(context.Background(), pnJID)
		if err != nil || lidJID.IsEmpty() {
			skipped++
			if syncLog != nil {
				syncLog.Printf("[RECONCILE]   %s → LID lookup failed (err=%v), skipping", pn.jid, err)
			}
			continue
		}

		lidStr := lidJID.String()

		// Check if a LID row already exists (created by app state events)
		var lidExists bool
		var lidArchived bool
		var lidPinned bool
		var lidMuteEnd int64
		err = messageStore.db.QueryRow(
			`SELECT is_archived, is_pinned, mute_end_time FROM chats WHERE jid = ?`, lidStr,
		).Scan(&lidArchived, &lidPinned, &lidMuteEnd)
		lidExists = err == nil

		// Use a transaction with deferred FK checks so we can rename
		// chats.jid and messages.chat_jid atomically without FK violations.
		tx, err := messageStore.db.Begin()
		if err != nil {
			skipped++
			continue
		}
		tx.Exec(`PRAGMA defer_foreign_keys = ON`)

		if lidExists {
			// Merge: LID row has authoritative metadata (from app state),
			// PN row has the real name and messages.

			// Step 1: Migrate any messages on the orphan LID row to the PN row
			tx.Exec(`UPDATE OR IGNORE messages SET chat_jid = ? WHERE chat_jid = ?`, pn.jid, lidStr)
			tx.Exec(`DELETE FROM messages WHERE chat_jid = ?`, lidStr)

			// Step 2: Delete the orphan LID row
			tx.Exec(`DELETE FROM chats WHERE jid = ?`, lidStr)

			// Step 3: Rename PN row to LID, applying LID row's authoritative metadata
			tx.Exec(
				`UPDATE chats SET jid = ?, is_archived = ?, is_pinned = ?, mute_end_time = ? WHERE jid = ?`,
				lidStr, lidArchived, lidPinned, lidMuteEnd, pn.jid)

			// Step 4: Update message foreign keys to point to the new LID jid
			tx.Exec(`UPDATE messages SET chat_jid = ? WHERE chat_jid = ?`, lidStr, pn.jid)

			if err := tx.Commit(); err != nil {
				tx.Rollback()
				if syncLog != nil {
					syncLog.Printf("[RECONCILE]   %s → MERGE FAILED: %v", pn.jid, err)
				}
				skipped++
				continue
			}

			if syncLog != nil {
				syncLog.Printf("[RECONCILE]   %s → %s MERGED (archived=%v pinned=%v name=%s)", pn.jid, lidStr, lidArchived, lidPinned, pn.name)
			}
			merged++
		} else {
			// No LID row exists — rename PN row to LID and update message FKs
			tx.Exec(`UPDATE chats SET jid = ? WHERE jid = ?`, lidStr, pn.jid)
			tx.Exec(`UPDATE messages SET chat_jid = ? WHERE chat_jid = ?`, lidStr, pn.jid)

			if err := tx.Commit(); err != nil {
				tx.Rollback()
				if syncLog != nil {
					syncLog.Printf("[RECONCILE]   %s → RENAME FAILED: %v", pn.jid, err)
				}
				skipped++
				continue
			}

			if syncLog != nil {
				syncLog.Printf("[RECONCILE]   %s → %s RENAMED", pn.jid, lidStr)
			}
			renamed++
		}
	}

	summary := fmt.Sprintf("[RECONCILE] Done: %d PN rows processed — merged=%d renamed=%d skipped=%d",
		len(pnRows), merged, renamed, skipped)
	fmt.Println(summary)
	if syncLog != nil {
		syncLog.Println(summary)
	}
}

// backfillContactNames iterates over all chats whose name is still a phone number
// and tries to resolve a real name from whatsmeow's contact store.
func backfillContactNames(client *whatsmeow.Client, messageStore *MessageStore, logger waLog.Logger) {
	contacts, err := client.Store.Contacts.GetAllContacts(context.Background())
	if err != nil {
		logger.Warnf("Failed to get contacts for backfill: %v", err)
		return
	}

	updated := 0
	for jid, info := range contacts {
		name := info.FullName
		if name == "" {
			name = info.PushName
		}
		if name == "" {
			name = info.BusinessName
		}
		if name == "" {
			continue
		}

		chatJID := messageStore.NormalizeJID(jid)
		err := messageStore.UpdateChatName(chatJID, name)
		if err != nil {
			logger.Warnf("Backfill: failed to update %s: %v", chatJID, err)
		} else {
			updated++
		}
	}

	if updated > 0 {
		logger.Infof("Contact backfill: updated %d chat names from %d contacts", updated, len(contacts))
	}
}

// Request history sync from the server
func requestHistorySync(client *whatsmeow.Client) {
	if client == nil {
		fmt.Println("Client is not initialized. Cannot request history sync.")
		return
	}

	if !client.IsConnected() {
		fmt.Println("Client is not connected. Please ensure you are connected to WhatsApp first.")
		return
	}

	if client.Store.ID == nil {
		fmt.Println("Client is not logged in. Please scan the QR code first.")
		return
	}

	// Build and send a history sync request
	historyMsg := client.BuildHistorySyncRequest(nil, 100)
	if historyMsg == nil {
		fmt.Println("Failed to build history sync request.")
		return
	}

	_, err := client.SendMessage(context.Background(), types.JID{
		Server: "s.whatsapp.net",
		User:   "status",
	}, historyMsg)

	if err != nil {
		fmt.Printf("Failed to request history sync: %v\n", err)
	} else {
		fmt.Println("History sync requested. Waiting for server response...")
	}
}

// analyzeOggOpus tries to extract duration and generate a simple waveform from an Ogg Opus file
func analyzeOggOpus(data []byte) (duration uint32, waveform []byte, err error) {
	// Try to detect if this is a valid Ogg file by checking for the "OggS" signature
	// at the beginning of the file
	if len(data) < 4 || string(data[0:4]) != "OggS" {
		return 0, nil, fmt.Errorf("not a valid Ogg file (missing OggS signature)")
	}

	// Parse Ogg pages to find the last page with a valid granule position
	var lastGranule uint64
	var sampleRate uint32 = 48000 // Default Opus sample rate
	var preSkip uint16 = 0
	var foundOpusHead bool

	// Scan through the file looking for Ogg pages
	for i := 0; i < len(data); {
		// Check if we have enough data to read Ogg page header
		if i+27 >= len(data) {
			break
		}

		// Verify Ogg page signature
		if string(data[i:i+4]) != "OggS" {
			// Skip until next potential page
			i++
			continue
		}

		// Extract header fields
		granulePos := binary.LittleEndian.Uint64(data[i+6 : i+14])
		pageSeqNum := binary.LittleEndian.Uint32(data[i+18 : i+22])
		numSegments := int(data[i+26])

		// Extract segment table
		if i+27+numSegments >= len(data) {
			break
		}
		segmentTable := data[i+27 : i+27+numSegments]

		// Calculate page size
		pageSize := 27 + numSegments
		for _, segLen := range segmentTable {
			pageSize += int(segLen)
		}

		// Check if we're looking at an OpusHead packet (should be in first few pages)
		if !foundOpusHead && pageSeqNum <= 1 {
			// Look for "OpusHead" marker in this page
			pageData := data[i : i+pageSize]
			headPos := bytes.Index(pageData, []byte("OpusHead"))
			if headPos >= 0 && headPos+12 < len(pageData) {
				// Found OpusHead, extract sample rate and pre-skip
				// OpusHead format: Magic(8) + Version(1) + Channels(1) + PreSkip(2) + SampleRate(4) + ...
				headPos += 8 // Skip "OpusHead" marker
				// PreSkip is 2 bytes at offset 10
				if headPos+12 <= len(pageData) {
					preSkip = binary.LittleEndian.Uint16(pageData[headPos+10 : headPos+12])
					sampleRate = binary.LittleEndian.Uint32(pageData[headPos+12 : headPos+16])
					foundOpusHead = true
					fmt.Printf("Found OpusHead: sampleRate=%d, preSkip=%d\n", sampleRate, preSkip)
				}
			}
		}

		// Keep track of last valid granule position
		if granulePos != 0 {
			lastGranule = granulePos
		}

		// Move to next page
		i += pageSize
	}

	if !foundOpusHead {
		fmt.Println("Warning: OpusHead not found, using default values")
	}

	// Calculate duration based on granule position
	if lastGranule > 0 {
		// Formula for duration: (lastGranule - preSkip) / sampleRate
		durationSeconds := float64(lastGranule-uint64(preSkip)) / float64(sampleRate)
		duration = uint32(math.Ceil(durationSeconds))
		fmt.Printf("Calculated Opus duration from granule: %f seconds (lastGranule=%d)\n",
			durationSeconds, lastGranule)
	} else {
		// Fallback to rough estimation if granule position not found
		fmt.Println("Warning: No valid granule position found, using estimation")
		durationEstimate := float64(len(data)) / 2000.0 // Very rough approximation
		duration = uint32(durationEstimate)
	}

	// Make sure we have a reasonable duration (at least 1 second, at most 300 seconds)
	if duration < 1 {
		duration = 1
	} else if duration > 300 {
		duration = 300
	}

	// Generate waveform
	waveform = placeholderWaveform(duration)

	fmt.Printf("Ogg Opus analysis: size=%d bytes, calculated duration=%d sec, waveform=%d bytes\n",
		len(data), duration, len(waveform))

	return duration, waveform, nil
}

// min returns the smaller of x or y
func min(x, y int) int {
	if x < y {
		return x
	}
	return y
}

// placeholderWaveform generates a synthetic waveform for WhatsApp voice messages
// that appears natural with some variability based on the duration
func placeholderWaveform(duration uint32) []byte {
	// WhatsApp expects a 64-byte waveform for voice messages
	const waveformLength = 64
	waveform := make([]byte, waveformLength)

	// Seed the random number generator for consistent results with the same duration
	rand.Seed(int64(duration))

	// Create a more natural looking waveform with some patterns and variability
	// rather than completely random values

	// Base amplitude and frequency - longer messages get faster frequency
	baseAmplitude := 35.0
	frequencyFactor := float64(min(int(duration), 120)) / 30.0

	for i := range waveform {
		// Position in the waveform (normalized 0-1)
		pos := float64(i) / float64(waveformLength)

		// Create a wave pattern with some randomness
		// Use multiple sine waves of different frequencies for more natural look
		val := baseAmplitude * math.Sin(pos*math.Pi*frequencyFactor*8)
		val += (baseAmplitude / 2) * math.Sin(pos*math.Pi*frequencyFactor*16)

		// Add some randomness to make it look more natural
		val += (rand.Float64() - 0.5) * 15

		// Add some fade-in and fade-out effects
		fadeInOut := math.Sin(pos * math.Pi)
		val = val * (0.7 + 0.3*fadeInOut)

		// Center around 50 (typical voice baseline)
		val = val + 50

		// Ensure values stay within WhatsApp's expected range (0-100)
		if val < 0 {
			val = 0
		} else if val > 100 {
			val = 100
		}

		waveform[i] = byte(val)
	}

	return waveform
}
