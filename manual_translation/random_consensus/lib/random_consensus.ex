defmodule Server do

  @vae_init true
  def main do
    p1 = spawn(Node, :start, [])
    p2 = spawn(Node, :start, [])
    p3 = spawn(Node, :start, [])
    p4 = spawn(Node, :start, [])
    nodes = [p1, p2, p3, p4]
    for node <- nodes do send node, { :BIND, nodes, self() } end
    receive do
      {:done, leader} -> IO.puts "Done"
    end
  end
end

defmodule Node do
  def start do
    receive do
      {:BIND, nodes, server} -> next nodes, server
    end
  end

  def next(nodes, server) do
    # Randomly vote for one of the nodes
    vote = Enum.random(nodes)
    for node <- nodes do
      send node, {:VOTE, vote}
    end
    # Receive votes from all nodes, terminate if all votes are the same
    votes = Enum.map(nodes, fn node -> receive do {:VOTE, vote} -> vote end end)
    if Enum.all?(votes, fn vote -> vote == Enum.at(votes, 0) end) do
      send server, {:done, Enum.at(votes, 0)}
    else
      next nodes, server
    end
  end
end
