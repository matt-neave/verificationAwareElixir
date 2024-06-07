import VaeLib

defmodule Server8 do
  @v_entry true
  @ltl "(q)U([]p)"
  @spec start_server() :: :ok
  @params {:client_n, :number_of_rounds}
  def start_server do
    client_n = 3
    number_of_rounds = 1
    alive_clients = 0
    predicate p, alive_clients == client_n * number_of_rounds
    predicate q, !p
    for _ <- 1..client_n do
      client = spawn(Client8, :start_client, [])
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

defmodule Client8 do
  @spec start_client() :: :ok
  def start_client do
    {server, rounds} = receive do
      {:bind, sender, round_limit} -> {sender, round_limit}
    end
    next_round(server, rounds)
  end

  @spec next_round(pid(), integer()) :: :ok
  defv next_round(server, rounds), pre: rounds >= 0 do
    if rounds == 0 do
      :ok
    else
      send(server, {:im_alive})
      next_round(server, rounds - 1)
    end
  end
end
