add_library(lsp
    InputHandler.cpp
    InputHandler.h
    Logger.h
    MessageParser.cpp
    MessageParser.h
    OutputGenerator.cpp
    OutputGenerator.h
    README.md
    Range.h
    Server.cpp
    Server.h
    TextBuffer.h
    Transport.cpp
    Transport.h
    VFS.cpp
    VFS.h
    protocol.h
)

target_link_libraries(lsp PUBLIC jsoncpp solutil)
target_include_directories(lsp PUBLIC "${CMAKE_PROJECT_ROOT}")
