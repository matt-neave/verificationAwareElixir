defmodule Client do

  @spec start_client(integer()) :: :ok
  def start_client(n_msgs) do
    receive do
      {:broadcast, sender} ->
        send sender, {:ack, self()}
    end
  end
end

defmodule Server do
  @spec start_server(integer(), integer()) :: :ok
  def start_server(n_clients, coordinator) do
    clients = receive do
      {:bind, clients} -> clients
    end

    for client <- clients do
      send client, {:broadcast, self()}
    end

    receive_acks(n_clients)

    send coordinator, {:server_done, self()}
  end

  @spec receive_acks(integer()) :: :ok
  def receive_acks(clients_remaining) do
    if clients_remaining == 0 do
      :ok
    else
      receive do
        {:ack, sender} ->
          receive_acks(clients_remaining - 1)
      end
    end
  end
end

defmodule Coordinator do

  @init true
  @spec start_coordinator() :: :ok
  def start_coordinator do
    client_count = 100
    server_count = 10
    load = 10

    servers = for server <- 1..server_count do
      spawn(Server, :start_server, [load, self()])
    end

    bind_servers(servers, server_count, load)

    for _ <- 1..server_count do
      receive do
        {:server_done, server} -> :ok
      end
    end
    IO.puts "All servers done"
  end

  @spec bind_servers(list(), integer(), integer()) :: :ok
  def bind_servers(servers, remaining, load) do
    if remaining == 0 do
      :ok
    else
      i = remaining - 1
      server = Enum.at(servers, i)
      clients = for _ <- 1..load do
        spawn(Client, :start_client, [load])
      end
      send server, {:bind, clients}
      bind_servers(servers, remaining - 1, load)
    end
  end
end
