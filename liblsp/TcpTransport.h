#pragma once

#include <liblsp/Transport.h>

#include <boost/asio.hpp>
#include <optional>

namespace lsp {

class TcpTransport: public Transport
{
public:
	explicit TcpTransport(unsigned short _port, std::function<void(std::string_view)> = {});

	bool closed() const noexcept override;
	std::optional<Json::Value> receive() override;
	void notify(std::string const& _method, Json::Value const& _params) override;
	void reply(MessageId const& _id, Json::Value const& _result) override;
	void error(MessageId const& _id, protocol::ErrorCode _code, std::string const& _message) override;

private:
	boost::asio::io_service m_io_service;
	boost::asio::ip::tcp::endpoint m_endpoint;
	boost::asio::ip::tcp::acceptor m_acceptor;
	std::optional<boost::asio::ip::tcp::iostream> m_stream;
	std::optional<JSONTransport> m_jsonTransport;
	std::function<void(std::string_view)> m_trace;
};

} // end namespace
