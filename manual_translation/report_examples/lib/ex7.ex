import VaeLib

defmodule Server7 do
  @init true
  @spec start_server() :: :ok
  @ltl "(q)U([]p)"
  def start_server do
    client_n = 3
    alive_clients = 0
    number_of_rounds = 2
    predicate p, alive_clients == client_n
    predicate q, !p
    for _ <- 1..client_n do
      client = spawn(Client7, :start_client, [])
      send(client, {:bind, self(), number_of_rounds})
    end
    alive_clients = check_clients(client_n * number_of_rounds, alive_clients)
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

defmodule Client7 do
  @spec start_client() :: :ok
  def start_client do
    {server, rounds} = receive do
      {:bind, sender, round_limit} -> {sender, round_limit}
    end
    next_round(server, rounds)
  end

  @spec next_round(pid(), integer()) :: :ok
  defv next_round(server, rounds), pre: rounds >= 0 do
    send(server, {:im_alive})
    next_round(server, rounds - 1)
  end
end
