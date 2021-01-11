#pragma once

#include <liblsp/Range.h>

#include <json/value.h>

#include <any>
#include <array>
#include <optional>
#include <map>
#include <string>
#include <variant>
#include <vector>

// NOTE: https://microsoft.github.io/language-server-protocol/specifications/specification-3-14/

namespace lsp {
	using MessageId = std::variant<int, std::string>;
}

namespace lsp::protocol {

using DocumentUri = std::string; // such as "file:///path/to"

enum class Trace { Off, Messages, Verbose };

enum class MessageType {
	Error = 1,
	Warning = 2,
	Info = 3,
	Log = 4,
};

constexpr inline std::string_view to_string(MessageType _type) noexcept
{
	switch (_type)
	{
		case MessageType::Error: return "Error";
		case MessageType::Warning: return "Warning";
		case MessageType::Info: return "Info";
		case MessageType::Log: return "Log";
		default: return "Unknown";
	}
}

/// Known error codes for an `InitializeError`
struct InitializeError {
	enum Code {
		/**
		 * If the protocol version provided by the client can't be handled by the server.
		 * @deprecated This initialize error got replaced by client capabilities. There is
		 * no version handshake in version 3.0x
		 */
		UnknownProtocolVersion = 1,
	};
	Code code;
	bool retry;
};

/// A workspace or project with its name and URI root.
struct WorkspaceFolder {
	std::string name; // The name of the workspace folder. Used to refer to this workspace folder in the user interface.
	DocumentUri uri;  // The associated URI for this workspace folder.
};

/// The initialize request is sent as the first request from the client to the server.
struct InitializeRequest {
	MessageId requestId;
	std::optional<int> processId;
	std::optional<std::string> rootPath;
	std::optional<DocumentUri> rootUri;
	std::optional<std::any> initializationOptions; // User provided initialization options.
	//TODO: ClientCapabilities capabilities; // The capabilities provided by the client (editor or tool)
	Trace trace = Trace::Off; // The initial trace setting. If omitted trace is disabled ('off').  // TODO: ^^ should be overridable by the solls CLI param
	std::vector<WorkspaceFolder> workspaceFolders; // initial configured workspace folders
};

/// Notification being sent when the client has finished initializing.
struct InitializedNotification {};

/// Defines how the host (editor) should sync document changes to the language server.
enum class TextDocumentSyncKind {
	None = 0,
	Full = 1,
	Incremental = 2
};

struct TextDocumentSyncOptions {
	bool openClose;
	TextDocumentSyncKind change;
};

struct TextDocumentSyncClientCapabilities {
	std::optional<bool> dynamicRegistration;
	std::optional<bool> willSave;
	std::optional<bool> willSaveWaitUntil;
	std::optional<bool> didSave;
};

struct WorkspaceFoldersServerCapabilities {
	bool supported = false;
	std::variant<std::string, bool> changeNotifications; // such as: `client/unregisterCapability`
};

struct WorkspaceCapabilities {
	std::optional<WorkspaceFoldersServerCapabilities> workspaceFolders;
};

struct ServerCapabilities {
	TextDocumentSyncOptions textDocumentSync;
	bool hoverProvider = false;
	bool definitionProvider; // ?: boolean | DefinitionOptions;
	// TODO ...
	WorkspaceCapabilities workspace;
};

struct ServerInfo {
	std::string name;
	std::optional<std::string> version;
};

struct InitializeResult {
	MessageId requestId;
	ServerCapabilities capabilities;
	std::optional<ServerInfo> serverInfo;
};

/// Represents a location inside a resource, such as a line inside a text file.
struct Location {
	DocumentUri uri;
	Range range;
};

/// Represents a link between a source and a target location.
struct LocationLink {
	std::optional<Range> originSelectionRange; // Span of the origin of this link.
	DocumentUri targetUri;                     // The target resource identifier of this link.
	Range targetRange;                         // The full target range of this link.
	Range targetSelectionRange;                // The range that should be selected and revealed when this link is being followed, e.g the name of a function.
};

enum class DiagnosticSeverity {
	Error = 1,
	Warning = 2,
	Information = 3,
	Hint = 4,
};

constexpr inline std::string_view to_string(DiagnosticSeverity _value) noexcept
{
	switch (_value)
	{
		case DiagnosticSeverity::Error: return "Error";
		case DiagnosticSeverity::Warning: return "Warning";
		case DiagnosticSeverity::Information: return "Info";
		case DiagnosticSeverity::Hint: return "Hint";
		default: return "Unknown";
	}
}

/// Represents a related message and source code location for a diagnostic. This should be
/// used to point to code locations that cause or related to a diagnostics, e.g when duplicating
/// a symbol in a scope.
struct DiagnosticRelatedInformation {
	Location location;   // The location of this related diagnostic information.
	std::string message; // The message of this related diagnostic information.
};

enum class DiagnosticTag {
	Unnecessary = 1, // Unused or unnecessary code.
	Deprecated = 2   // Deprecated or obsolete code.
};

/// Represents a diagnostic, such as a compiler error or warning. Diagnostic objects are only valid in the scope of a resource.
struct Diagnostic {
	Range range; // The range at which the message applies.
	std::optional<DiagnosticSeverity> severity;
	std::variant<int, std::string, std::monostate> code; // The diagnostic's code, which might appear in the user interface.
	std::optional<std::string> source; // A human-readable string describing the source of this diagnostic, e.g. 'typescript' or 'super lint'.
	std::string message; // The diagnostic's message.
	std::vector<DiagnosticTag> diagnosticTag; // Additional metadata about the diagnostic.
	std::vector<DiagnosticRelatedInformation> relatedInformation; // An array of related diagnostic information, e.g. when symbol-names within a scope collide all definitions can be marked via this property.
};

struct PublishDiagnosticsClientCapabilities
{
	struct TagSupport {
		std::vector<DiagnosticTag> valueSet; // The tags supported by the client.
	};

	bool relatedInformation;              // Whether the clients accepts diagnostics with related information.
	std::optional<TagSupport> tagSupport; // Client supports the tag property to provide meta data about a diagnostic.
	std::optional<bool> versionSupport;   // Whether the client interprets the version property of the `textDocument/publishDiagnostics` notification's parameter.
};

struct PublishDiagnosticsParams {
	DocumentUri uri; // The URI for which diagnostic information is reported.
	std::optional<int> version = std::nullopt; // Optional the version number of the document the diagnostics are published for.
	std::vector<Diagnostic> diagnostics = {}; // An array of diagnostic information items.
};

/// A textual edit applicable to a text document.
struct TextEdit {
	Range range; // The range of the text document to be manipulated. To insert text into a document create a range where start === end.
	std::string newText; // The string to be inserted. For delete operations use an empty string.
};

/// Text documents are identified using a URI.
struct TextDocumentIdentifier {
	DocumentUri uri;
};

struct VersionedTextDocumentIdentifier : TextDocumentIdentifier {
	/**
	 * The version number of this document. If a versioned text document identifier
	 * is sent from the server to the client and the file is not open in the editor
	 * (the server has not received an open notification before) the server can send
	 * `null` to indicate that the version is known and the content on disk is the
	 * truth (as speced with document content ownership).
	 *
	 * The version number of a document will increase after each change, including
	 * undo/redo. The number doesn't need to be consecutive.
	 */
	std::optional<int> version;
};

/// Describes textual changes on a single text document.
struct TextDocumentEdit {
	VersionedTextDocumentIdentifier textDocument; // The text document to change.
	std::vector<TextEdit> edits; // The edits to be applied.
};

// -----------------------------------------------------------------------------------------------
// File Reosurce Changes
// ---------------------
// New in 3.13

/// Options to create a file.
struct CreateFileOptions {
	std::optional<bool> overwrite;      // Overwrite existing file. Overwrite wins over `ignoreIfExists`
	std::optional<bool> ignoreIfExists; // Ignore if exists.
};

/// Create file operation
struct CreateFile {
	DocumentUri uri; // The resource to create.
	std::optional<CreateFileOptions> options; // Additional options
};

/// Rename file operation
struct RenameFile {
	DocumentUri oldUri;                       // The old (existing) location.
	DocumentUri newUri;                       // The new location.

	// options
	std::optional<bool> overwrite;            // Overwrite target if existing. Overwrite wins over `ignoreIfExists`
	std::optional<bool> ignoreIfExists;       // Ignores if target exists.
};

/// Delete file operation
struct DeleteFile {
	DocumentUri uri;

	// options
	std::optional<bool> recursive; // Delete the content recursively if a folder is denoted.
	std::optional<bool> ignoreIfNotExists; // Ignore the operation if the file doesn't exist.
};

// -----------------------------------------------------------------------------------------------

/// A workspace edit represents changes to many resources managed in the workspace.
///
/// The edit should either provide `changes` or `documentChanges`.
/// If the client can handle versioned document edits and if `documentChanges` are present,
/// the latter are preferred over `changes`.
struct WorkspaceEdit {
	std::map<DocumentUri, std::vector<TextEdit>> changes;

	using Change = std::variant<
		TextDocumentEdit,
		CreateFile,
		RenameFile,
		DeleteFile
	>;

	std::variant<
		std::vector<TextDocumentEdit>, // TODO: I think we can map this to the variant below
		std::vector<Change>
	> documentChanges;
};

/// An item to transfer a text document from the client to the server.
struct TextDocumentItem {
	DocumentUri uri;        // The text document's URI.
	std::string languageId; // The text document's language identifier.
	int version;            // The version number of this document (it will increase after each change, including undo/redo).
	std::string text;       // The content of the opened text document.
};

/// A parameter literal used in requests to pass a text document and a position inside that document.
struct TextDocumentPositionParams {
	TextDocumentIdentifier textDocument; // The text document.
	Position position; // The position inside the text document.
};

/// Describes the content type that a client supports in various result literals like `Hover`, `ParameterInfo` or `CompletionItem`.
enum class MarkupKind {
	PlainText, // Plain text is supported as a content format
	Markdown   // Markdown is supported as a content format
};

/// A `MarkupContent` literal represents a string value which content is interpreted base on its kind flag.
struct MarkupContent {
	MarkupKind kind;   // The type of the Markup
	std::string value; // The content itself
};

/// An event describing a change to a text document.
/// If range and rangeLength are omitted the new text is considered to be the full content of the document.
struct TextDocumentRangedContentChangeEvent {
	MessageId requestId;
	Range range;                    // The range of the document that changed.
	std::optional<int> rangeLength; // The optional length of the range that got replaced (deprecated).
	std::string text;               // The new text for the provided range.
};

struct TextDocumentFullContentChangeEvent {
	MessageId requestId;
	std::string text;    // The new text of the whole document.
};

using TextDocumentContentChangeEvent = std::variant<
	TextDocumentRangedContentChangeEvent,
	TextDocumentFullContentChangeEvent
>;

// -----------------------------------------------------------------------------------------------

struct DidOpenTextDocumentParams {
	MessageId requestId;
	TextDocumentItem textDocument; // The document that was opened.
};

/// The document close notification is sent from the client to the server when the document got closed in the client.
struct DidCloseTextDocumentParams {
	MessageId requestId;
	TextDocumentIdentifier textDocument;
};

struct DidChangeTextDocumentParams {
	MessageId requestId;
	VersionedTextDocumentIdentifier textDocument; // The document that did change. The version number points to the version after all provided content changes have been applied.
	std::vector<TextDocumentContentChangeEvent> contentChanges; // The actual content changes.
};

struct LogMessageParams {
	MessageType type; // The message type.
	std::string message; // The actual message
};

/// The client requested a shutdown (without terminating). Only `Exit` event is valid after this.
struct ShutdownParams {};

/// The client requested the server to terminate.
struct ExitParams {};

/// Artificial request that is being received upon an invalid request.
/// The server MUST respond with an ErrorCode::InvalidRequest.
struct InvalidRequest
{
	MessageId requestId;    // JSON-RPC request ID that was invalid.
	std::string methodName; // JSON-RPC method that was invalid.
};

enum class ErrorCode
{
	// Defined by JSON RPC
	ParseError = -32700,
	InvalidRequest = -32600,
	MethodNotFound = -32601,
	InvalidParams = -32602,
	InternalError = -32603,
	serverErrorStart = -32099,
	serverErrorEnd = -32000,
	ServerNotInitialized = -32002,
	UnknownErrorCode = -32001,

	// Defined by the protocol.
	RequestCancelled = -32800,
	ContentModified = -32801,
};

/// DefinitionParams is Used for request and response.
struct DefinitionParams : TextDocumentPositionParams {
	MessageId requestId;
};

struct DefinitionReplyParams {
	DocumentUri uri;
	Range range;
};

// -----------------------------------------------------------------------------------------------

/// Message for cancelling a request. This can be sent in both directions.
struct CancelRequest {
	MessageId id;
};

using Request = std::variant<
	CancelRequest,
	DefinitionParams,
	DidChangeTextDocumentParams,
	DidCloseTextDocumentParams,
	DidOpenTextDocumentParams,
	InitializeRequest,
	InitializedNotification,
	InvalidRequest
	// TODO ...
>;

using Response = std::variant<
	// TODO ...
	DefinitionReplyParams,
	InitializeResult
>;

using Notification = std::variant<
	// TODO ...
	CancelRequest,
	ExitParams,
	LogMessageParams,
	PublishDiagnosticsParams,
	ShutdownParams
>;

} // end namespace
