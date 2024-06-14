defmodule RaftNode3 do
  @spec start_node(integer(), integer(), integer()) :: :ok
  def start_node(id, n_peers, client) do
    peers = receive do
      {:bind, peers} -> peers
    end
    term = 10 * id
    node_handler(id, peers, n_peers, 0, term, 0, client)
  end

  @spec node_handler(integer(), list(), integer(), atom(), integer(), integer(), integer()) :: :ok
  defp node_handler(id, peers, n_peers, state, term, vote_count, client) do
    receive do
      {:request_vote, candidate_term, candidate_id, reply_to} ->
        if candidate_term > term do
          send(reply_to, {:vote_granted, id})
          node_handler(id, peers, n_peers, 0, candidate_term, vote_count, client)
        else
          node_handler(id, peers, n_peers, state, term, vote_count, client)
        end

      {:vote_granted, _voter_id} ->
        new_vote_count = vote_count + 1
        if state == 1 and new_vote_count >= n_peers / 2 + 1 do
          send(client, {:elected, term})
          for peer <- peers do
            send(peer, {:append_entries, term, id}) # Send log here
          end
          node_handler(id, peers, n_peers, 2, term, new_vote_count, client)
        else
          node_handler(id, peers, n_peers, state, term, new_vote_count, client)
        end

      {:start_election} ->
        for peer <- peers do
          send(peer, {:request_vote, term + 1, id, self()})
        end
        node_handler(id, peers, n_peers, 1, term + 1, 0, client)

      {:terminate} ->
        IO.puts("Terminating node")

      after 1000 ->
        send self(), {:start_election}
        node_handler(id, peers, n_peers, state, term, 0, client)
    end
  end
end

defmodule Client3 do
  @init true
  @spec start() :: :ok
  @ltl """
  !<>[](elected_term == previously_elected_term)
  """
  def start do
    # follower -> 0, candidate -> 1, leader -> 2
    n_nodes = 3
    n_peers = n_nodes - 1
    rounds = 2
    previously_elected_term = -1
    elected_term = 0
    nodes = for id <- 1..n_nodes do
      spawn(RaftNode3, :start_node, [id, n_peers, self()])
    end

    for p_id <- nodes do
      send(p_id, {:bind, nodes})
    end

    for _ <- 1..rounds do
      {elected_term, previously_elected_term} = receive do
        {:elected, term} ->
          IO.puts("Node elected")
          {term, elected_term}
      end
    end

    for p_id <- nodes do
      send(p_id, {:terminate})
    end
  end
end
