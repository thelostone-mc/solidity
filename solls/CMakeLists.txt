add_subdirectory(lsp)

add_executable(solls
	LanguageServer.cpp LanguageServer.h
	main.cpp
)
target_link_libraries(solls PRIVATE lsp solidity Boost::boost Boost::program_options)
target_include_directories(solls PRIVATE "${CMAKE_PROJECT_ROOT}")

include(GNUInstallDirs)
install(TARGETS solc DESTINATION "${CMAKE_INSTALL_BINDIR}")

if(SOLC_LINK_STATIC AND UNIX AND NOT APPLE)
	# Produce solls as statically linked binary (includes C/C++ standard libraries)
	# This is not supported on macOS, see
	# https://developer.apple.com/library/content/qa/qa1118/_index.html.
	set_target_properties(
		solls PROPERTIES
		LINK_FLAGS -static
		LINK_SEARCH_START_STATIC ON
		LINK_SEARCH_END_STATIC ON
	)
endif()
