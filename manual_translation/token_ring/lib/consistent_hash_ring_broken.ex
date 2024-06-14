import VaeLib

defmodule ConsistentHashRingB do

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

      {:add_node, node} ->
        new_nodes = nodes ++ [node]
        new_node_position = hash(node)
        new_node_positions = node_positions ++ [new_node_position]
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

defmodule ClientB do

  @init true
  @spec start() :: :ok
  @ltl "[](r1 -> <>(p1))"
  @ltl "[](r2 -> <>(p3))"
  @ltl "[](r3 && n_nodes==3 -> <>(p1))"
  @ltl "[](r3 && n_nodes==4 -> <>(p4))"
  def start do
    n_nodes = 3
    nodes = for i <- 1..n_nodes do
      i
    end
    ring = spawn(ConsistentHashRingB, :start_ring, [nodes, n_nodes])

    next_key = 42
    send ring, {:lookup, next_key, self()}
    ring_position = receive do
      {:ring_pos, node} ->
        IO.puts("Key 42 is assigned to")
        IO.puts node
        node
    end

    next_key = 25
    send ring, {:lookup, next_key, self()}
    ring_position = receive do
      {:ring_pos, node} ->
        IO.puts("Key 25 is assigned to")
        IO.puts node
        node
    end

    next_key = 31
    send ring, {:lookup, next_key, self()}
    ring_position = receive do
      {:ring_pos, node} ->
        IO.puts("Key 31 is assigned to")
        IO.puts node
        node
    end

    # Dynamically grow the ring
    send ring, {:add_node, 4}
    n_nodes = n_nodes + 1

    next_key = 31
    send ring, {:lookup, next_key, self()}
    ring_position = receive do
      {:ring_pos, node} ->
        IO.puts("Key 31 is assigned to")
        IO.puts node
        node
    end

    predicate p1, ring_position == 1
    predicate p2, ring_position == 2
    predicate p3, ring_position == 3
    predicate p4, ring_position == 4
    predicate r1, next_key == 42
    predicate r2, next_key == 25
    predicate r3, next_key == 31

    send ring, {:terminate}
  end
end
