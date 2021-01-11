#pragma once
// XXX this file is purely kept in case I need some of those structs later. Remove file before merge.
#include <liblsp/protocol.h>

namespace lsp::protocol {
/**
 * Represents a reference to a command.
 * Provides a title which will be used to represent a command in the UI.
 * Commands are identified by a string identifier.
 * The recommended way to handle commands is to implement their execution on the server side
 * if the client and server provides the corresponding capabilities.
 * Alternatively the tool extension code could handle the command.
 * The protocol currently doesn’t specify a set of well-known commands.
 */
struct Command {
	/**
	 * Title of the command, like `save`.
	 */
	std::string title;

	/**
	 * The identifier of the actual command handler.
	 */
	std::string command;

	/**
	 * Arguments that the command handler should be
	 * invoked with.
	 */
	std::optional<std::vector<std::any>> arguments;
};

struct SaveOptions {
	bool includeText; // The client is supposed to include the content on save.
};

/// A document filter denotes a document through properties like language, scheme or pattern.
/// An example is a filter that applies to TypeScript files on disk.
/// Another example is a filter the applies to JSON files with name package.json:
///   { language: 'typescript', scheme: 'file' }
///   { language: 'json', pattern: '**/package.json' }
struct DocumentFilter {
	/**
	 * A language id, like `typescript`.
	 */
	std::optional<std::string> language;

	/**
	 * A Uri [scheme](#Uri.scheme), like `file` or `untitled`.
	 */
	std::optional<std::string> scheme;

	// A glob pattern, like `*.{ts,js}`.
	//
	// Glob patterns can have the following syntax:
	// - `*` to match one or more characters in a path segment
	// - `?` to match on one character in a path segment
	// - `**` to match any number of path segments, including none
	// - `{}` to group conditions (e.g. `**/*.{ts,js}` matches all TypeScript and JavaScript files)
	// - `[]` to declare a range of characters to match in a path segment (e.g., `example.[0-9]` to match on `example.0`, `example.1`, …)
	// - `[!...]` to negate a range of characters to match in a path segment (e.g., `example.[!0-9]` to match on `example.a`, `example.b`, but not `example.0`)
	std::optional<std::string> pattern;
};

/// A document selector is the combination of one or more document filters.
using DocumentSelector = std::vector<DocumentFilter>;


}
