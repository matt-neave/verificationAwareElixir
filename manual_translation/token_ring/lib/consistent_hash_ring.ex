defmodule ConsistentHashRing do

  @spec start_ring(list()) :: :ok
  def start_ring(nodes) do
    node_positions = Enum.map(nodes, fn n -> hash(n) end)
    ring_handler(nodes, node_positions)
  end

  @spec ring_handler(list(), list()) :: :ok
  defp ring_handler(nodes, node_positions) do
    receive do
      {:lookup, key, sender} ->
        position = hash(key)
        node = find_closest_node(nodes, node_positions, position, 0)
        send sender, {:node, node}
        ring_handler(nodes, node_positions)

      {:terminate} ->
        IO.puts("Terminating ring handler")
    end
  end

  @spec find_closest_node(list(), list(), integer(), integer()) :: integer()
  defp find_closest_node(nodes, node_positions, position, i) do
    n_nodes = 2

    if i >= n_nodes do
      Enum.at(nodes, 0)
    else
      n = Enum.at(nodes, i)
      p = Enum.at(node_positions, i)

      if p >= position do
        n
      else
        find_closest_node(nodes, node_positions, position, i + 1)
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
      2 -> 9
      3 -> 5
    end
  end


end

defmodule Client do

  @vae_init true
  @spec start() :: :ok
  def start do
    nodes = [1, 2]
    ring = spawn(ConsistentHashRing, :start_ring, [nodes])

    next_key = 42
    send ring, {:lookup, next_key, self()}
    ring_position = receive do
      {:node, node} ->
        IO.puts("Key 42 is assigned")
        node
    end

    next_key = 25
    send ring, {:lookup, next_key, self()}
    ring_position = receive do
      {:node, node} ->
        IO.puts("Key 25 is assigned")
        node
    end

    next_key = 31
    send ring, {:lookup, next_key, self()}
    ring_position = receive do
      {:node, node} ->
        IO.puts("Key 31 is assigned")
        node
    end

    send ring, {:terminate}
  end
end
