Set WshShell = CreateObject("WScript.Shell")
WshShell.CurrentDirectory = "C:\Dev\whatsapp-mcp\whatsapp-bridge"
WshShell.Run """C:\Dev\whatsapp-mcp\whatsapp-bridge\whatsapp-bridge.exe""", 0, False
