import VaeLib

defmodule ConsistentHashRingC do

  @spec start_ring(list(), integer()) :: :ok
  def start_ring(nodes, n) do
    node_positions = Enum.map(nodes, fn n -> hash(n) end)
    ring_handler(nodes, node_positions, n)
  end

  @spec ring_handler(list(), list(), integer()) :: :ok
  defp ring_handler(nodes, node_positions, n) do
    receive do
      {:lookup, key, sender} ->
        position = hash(key)
        node = find_closest_node(nodes, node_positions, position, 0, n)
        send sender, {:ring_pos, node}
        ring_handler(nodes, node_positions, n)

      {:add_node, node, sender} ->
        new_nodes = nodes ++ [node]
        new_node_position = hash(node)
        new_node_positions = node_positions ++ [new_node_position]
        send sender, {:node_accepted}
        ring_handler(new_nodes, new_node_positions, n + 1)

      {:terminate} ->
        IO.puts("Terminating ring handler")
    end
  end

  @spec find_closest_node(list(), list(), integer(), integer(), integer()) :: integer()
  defp find_closest_node(nodes, node_positions, position, i, n) do
    if i >= n do
      Enum.at(nodes, 0)
    else
      check_node = Enum.at(nodes, i)
      check_pos = Enum.at(node_positions, i)

      if check_pos >= position do
        check_node
      else
        find_closest_node(nodes, node_positions, position, i + 1, n)
      end
    end
  end

  @spec hash(integer()) :: integer()
  defp hash(key) do
    # Example hardcoded hash values for keys and nodes
    case key do
      # Keys
      42 -> 1
      25 -> 8
      31 -> 10

      # Nodes
      1 -> 2
      2 -> 5
      3 -> 9
      4 -> 15
    end
  end
end

defmodule ClientC do

  @init true
  @spec start() :: :ok
  @ltl "[](sent_request -> <>assigned_node)"
  def start do
    n_nodes = 3
    nodes = for i <- 1..n_nodes do
      i
    end
    ring = spawn(ConsistentHashRingC, :start_ring, [nodes, n_nodes])


    values = [42, 25, 31]
    sent_request = false
    assigned_node = false
    for v <- values do
      assigned_node= false
      send ring, {:lookup, v, self()}
      assigned_node = receive do
        {:ring_pos, node} ->
          true
        end
      sent_request = false
    end

    send ring, {:terminate}
  end
end
