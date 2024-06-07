defmodule Server3 do
  @v_entry true
  @spec start_server() :: :ok
  def start_server do
    client = spawn(Client, :start_client, [])
    send client, {:bind, self()}
    send client, {:you_go_next}
    server_go_next(client)
  end

  @spec server_go_next(integer()) :: :ok
  def server_go_next(client) do
    receive do
      {:you_go_next} ->
        send client, {:you_go_next}
        server_go_next(client)
      {:terminate} -> IO.puts "Server terminated"
    end
  end
end

defmodule Client3 do
  @spec start_client() :: :ok
  def start_client do
    receive do
      {:bind, server} -> client_go_next(server)
    end
  end

  @spec client_go_next(integer()) :: :ok
  def client_go_next(server) do
    receive do
      {:you_go_next} ->
        send server, {:you_go_next}
        client_go_next(server)
      {:terminate} -> IO.puts "This cant happen"
    end
  end
end
