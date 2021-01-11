#pragma once

#include <liblsp/protocol.h>
#include <liblsp/InputHandler.h>
#include <liblsp/OutputGenerator.h>
#include <liblsp/Logger.h>

#include <json/value.h>

#include <functional>
#include <iosfwd>
#include <optional>
#include <string>
#include <string_view>

namespace lsp {

/// Transport layer API
///
/// The transport layer API is abstracted so it users become more testable as well as
/// this way it could be possible to support other transports (HTTP for example) easily.
class Transport
{
public:
	virtual ~Transport() = default;

	/// @returns boolean indicating whether or not the underlying (input) stream is closed.
	virtual bool closed() const noexcept = 0;

	/// Reveives a message
	virtual std::optional<Json::Value> receive() = 0;
	// TODO: ^^ think about variant<Json::Value, Timeout, Closed, error_code> as return type instead

	/// Sends a notification message to the other end (client).
	virtual void notify(std::string const& _method, Json::Value const& _params) = 0;

	/// Sends a reply message, optionally with a given ID to correlate this message to another from the other end.
	virtual void reply(MessageId const& _id, Json::Value const& _result) = 0;

	/// Sends an error reply with regards to the given request ID.
	virtual void error(MessageId const& _id, protocol::ErrorCode _code, std::string const& _message) = 0;
};

/// Standard stdio style JSON-RPC stream transport.
class JSONTransport: public Transport // TODO: Should be named: StdioTransport
{
public:
	/// Constructs a standard stream transport layer.
	///
	/// @param _in for example std::cin (stdin)
	/// @param _out for example std::cout (stdout)
	/// @param _trace special logger used for debugging the LSP messages.
	JSONTransport(std::istream& _in, std::ostream& _out, std::function<void(std::string_view)> _trace);

	bool closed() const noexcept override;
	std::optional<Json::Value> receive() override;
	void notify(std::string const& _method, Json::Value const& _params) override;
	void reply(MessageId const& _id, Json::Value const& _result) override;
	void error(MessageId const& _id, protocol::ErrorCode _code, std::string const& _message) override;

private:
	using HeaderMap = std::unordered_map<std::string, std::string>;

	/// Sends an arbitrary raw message to the client.
	///
	/// Used by the notify/reply/error function family.
	void send(Json::Value const& _message);

	/// Parses a single text line from the client ending with CRLF (or just LF).
	std::string readLine();

	/// Parses header section from the client including message-delimiting empty line.
	std::optional<HeaderMap> parseHeaders();

	/// Reads given number of bytes from the client.
	std::string readBytes(int _n);

	/// Appends given JSON message to the trace log.
	void traceMessage(Json::Value const& _message, std::string_view _title);

private:
	std::istream& m_input;
	std::ostream& m_output;
	std::function<void(std::string_view)> m_trace;
};

} // end namespace


