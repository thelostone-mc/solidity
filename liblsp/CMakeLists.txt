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
    TcpTransport.cpp
    TcpTransport.h
    VFS.cpp
    VFS.h
    protocol.h
)

target_link_libraries(lsp PUBLIC jsoncpp solutil Boost::system Threads::Threads)
target_include_directories(lsp PUBLIC "${CMAKE_PROJECT_ROOT}")
