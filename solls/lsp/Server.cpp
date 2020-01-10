#include <lsp/Server.h>
#include <lsp/OutputGenerator.h>
#include <lsp/Transport.h>

#include <libsolutil/Visitor.h>
#include <libsolutil/JSON.h>

#include <functional>
#include <ostream>

#include <iostream>

using namespace std;
using namespace std::placeholders;

namespace lsp {

Server::Server(Transport& _client):
	m_client{_client},
	m_inputHandler{*this}
{
}

int Server::run()
{
	while (!m_exitRequested)
	{
		// TODO: receive() must return a variant<> to also return on <Transport::TimeoutEvent>,
		// so that we can perform some idle tasks in the meantime, such as
		// - lazy validation runs
		// - check for results of asynchronous runs (in case we want to support threaded background jobs)
		// Also, EOF should be noted properly as a <Transport::ClosedEvent>.
		optional<Json::Value> const jsonMessage = client().receive();
		if (jsonMessage.has_value())
		{
			optional<protocol::Request> const message = m_inputHandler.handleRequest(*jsonMessage);
			if (message.has_value())
				visit(*this, message.value());
			else
				logError("Could not analyze RPC request.");
		}
		else
			logError("Could not read RPC request.");
	}

	if (m_shutdownRequested)
		return EXIT_SUCCESS;
	else
		return EXIT_FAILURE;
}

void Server::operator()(protocol::InvalidRequest const& _invalid)
{
	// The LSP specification requires an invalid request to be respond with an InvalidRequest error response.
	error(_invalid.requestId, protocol::ErrorCode::InvalidRequest, "Invalid request " + _invalid.methodName);
}

void Server::operator()(protocol::ShutdownParams const&)
{
	logInfo("Shutdown requested");
	m_shutdownRequested = true;
}

void Server::operator()(protocol::ExitParams const&)
{
	logInfo("Exit requested");
	m_exitRequested = true;
}

void Server::handleMessage(string const& _message)
{
	optional<protocol::Request> const message = m_inputHandler.handleRequest(_message);
	if (message.has_value())
		visit(*this, message.value());
	else
		logError("Could not analyze RPC request.");
}

void Server::reply(lsp::protocol::Id const& _id, lsp::protocol::Response const& _message)
{
	auto const json = m_outputGenerator(_message);
	m_client.reply(_id, json);
}

void Server::error(lsp::protocol::Id const& _id, lsp::protocol::ErrorCode _code, string  const& _message)
{
	m_client.error(_id, _code, _message);
}

void Server::notify(lsp::protocol::Notification const& _message)
{
	auto const [method, json] = m_outputGenerator(_message);
	m_client.notify(method, json);
}

void Server::log(protocol::MessageType _type, string const& _message)
{
	auto const [method, json] = m_outputGenerator(protocol::LogMessageParams{_type, _message});
	m_client.notify(method, json);
}

} // end namespace
