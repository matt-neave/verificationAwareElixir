defmodule RingClient do

  @spec start_client(integer()) :: :ok
  def start_client(n_msgs) do
    receive do
      {:broadcast, sender} ->
        send sender, {:ack, self()}
    end
  end
end

defmodule RingServer do
  @spec start_server(integer(), integer()) :: :ok
  def start_server(n_clients, coordinator) do
    receive do
      {:bind, clients, neighbour} -> server_loop(coordinator, n_clients, clients, neighbour)
    end
  end

  @spec server_loop(integer(), integer(), list(), integer()) :: :ok
  def server_loop(coordinator, n_clients, clients, neighbour) do
    receive do
      {:broadcast, sender} ->

        send neighbour, {:broadcast, self()}

        # Broadcast to own clients
        for client <- clients do
          send client, {:broadcast, self()}
        end
        receive_acks(n_clients)

        # Notify the coordinator once done
        send coordinator, {:server_done, self()}
    end
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

defmodule RingCoordinator do

  @init true
  @spec start_coordinator() :: :ok
  def start_coordinator do
    client_count = 100
    server_count = 10
    load = 10

    servers = for server <- 1..server_count do
      spawn(RingServer, :start_server, [load, self()])
    end

    bind_servers(servers, server_count, load, server_count)

    head = Enum.at(servers, 0)
    send head, {:broadcast, self()}

    for _ <- 1..server_count do
      receive do
        {:server_done, server} -> :ok
      end
    end
    IO.puts "All servers done"
  end

  @spec bind_servers(list(), integer(), integer(), integer()) :: :ok
  def bind_servers(servers, remaining, load, n_servers) do
    if remaining == 0 do
      :ok
    else
      i = remaining - 1
      server = Enum.at(servers, i)
      right_server_i = rem(i + 1, n_servers)
      right_server = Enum.at(servers, right_server_i)
      clients = for _ <- 1..load do
        spawn(RingClient, :start_client, [load])
      end
      send server, {:bind, clients, right_server}
      bind_servers(servers, remaining - 1, load, n_servers)
    end
  end
end
