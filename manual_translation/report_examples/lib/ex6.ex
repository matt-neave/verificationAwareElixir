defmodule Server6 do
  @vae_init true
  @spec start_server() :: :ok
  @ltl "(q)U([]p)"
  def start_server do
    client_n = 3
    alive_clients = 0
    predicate p, alive_clients == client_n
    predicate q, !p
    for _ <- 1..client_n do
      client = spawn(Client6, :start_client, [])
      send(client, {:bind, self()})
    end
    alive_clients = check_clients(client_n, alive_clients)
  end

  @spec check_clients(integer(), integer()) :: integer()
  def check_clients(expected_clients, current_clients) do
    if expected_clients == current_clients do
      current_clients
    else
      receive do
        {:im_alive} -> check_clients(expected_clients, current_clients + 1)
      end
    end
  end
end

defmodule Client6 do
  @spec start_client() :: :ok
  def start_client do
    server = receive do
      {:bind, sender} -> sender
    end
    send(server, {:im_alive})
  end
end
