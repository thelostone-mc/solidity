add_library(lsp
	InputHandler.h InputHandler.cpp
	MessageParser.h MessageParser.cpp
	OutputGenerator.h OutputGenerator.cpp
	Server.h Server.cpp
	TextBuffer.h
	Transport.h Transport.cpp
	VFS.h VFS.cpp
	protocol.h
)

target_link_libraries(lsp PUBLIC jsoncpp solutil)
target_include_directories(lsp PUBLIC ${CMAKE_CURRENT_SOURCE_DIR}/..)
