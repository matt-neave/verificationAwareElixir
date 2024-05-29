defmodule TRing do
  @hash_range 10

  def start_ring(nodes) do
    node_positions = assign_positions(nodes)
    ring_handler(nodes, node_positions)
  end

  defp assign_positions(nodes) do
    # Hardcoded positions for simplicity
    Enum.map(nodes, &hash/1)
  end

  defp ring_handler(nodes, node_positions) do
    receive do
      {:lookup, key, sender} ->
        position = hash(key)
        node = find_closest_node(nodes, node_positions, position)
        send sender, {:node, node}
        ring_handler(nodes, node_positions)

      {:add_node, node} ->
        position = hash(node)
        updated_nodes = [node | nodes]
        updated_positions = [position | node_positions]
        ring_handler(updated_nodes, updated_positions)

      {:remove_node, node} ->
        {updated_nodes, updated_positions} = remove_node(nodes, node_positions, node)
        ring_handler(updated_nodes, updated_positions)

      {:terminate} ->
        IO.puts("Terminating ring handler")
    end
  end

  defp remove_node([], positions, _node), do: {[], positions}

  defp remove_node([node | rest_nodes], [pos | rest_positions], node_to_remove) do
    if node == node_to_remove do
      remove_node(rest_nodes, rest_positions, node_to_remove)
    else
      {updated_nodes, updated_positions} = remove_node(rest_nodes, rest_positions, node_to_remove)
      {[node | updated_nodes], [pos | updated_positions]}
    end
  end

  defp hash(key) do
    # Example hardcoded hash values for keys and nodes
    case key do
      42 -> 2
      31 -> 10
      :node1 -> 2
      :node2 -> 9
      _ -> 0
    end
  end

  defp find_closest_node(nodes, positions, position) do
    find_closest_node(nodes, positions, position, nil, @hash_range, 0)
  end

  defp find_closest_node([], [], _position, closest_node, _closest_distance, _index), do: closest_node

  defp find_closest_node([node | rest_nodes], [node_position | rest_positions], position, closest_node, closest_distance, index) do
    current_distance = if node_position >= position, do: node_position - position, else: @hash_range - position + node_position
    if current_distance < closest_distance do
      find_closest_node(rest_nodes, rest_positions, position, node, current_distance, index + 1)
    else
      find_closest_node(rest_nodes, rest_positions, position, closest_node, closest_distance, index + 1)
    end
  end
end

# Example usage:

defmodule TClient do
  def start do
    nodes = [:node1, :node2]
    ring = spawn(ConsistentHashRing, :start_ring, [nodes])

    send ring, {:lookup, 42, self()}
    receive do
      {:node, node} ->
        IO.puts("Key 42 is assigned to #{node}")
    end

    send ring, {:lookup, 31, self()}
    receive do
      {:node, node} ->
        IO.puts("Key 31 is assigned to #{node}")
    end

    send ring, {:terminate}
  end
end
