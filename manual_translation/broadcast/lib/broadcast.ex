defmodule Broadcast do


  def start do
    n = 3
    max_broadcasts = 10
    recv = 0
    pids = for i <- 1..n do
      spawn Client, :init, []
    end
    for pid <- pids do
      send pid, {:bind, pids, max_broadcasts}
    end
    next recv, n
  end

  def next(recv, n) do
    unless recv == n do
      receive do
        {:finished} -> next recv + 1, n
      end
    end
  end
end

defmodule Client do

  def init do

    receive do
      {:bind, peers, broadcasts} ->
        counts = Enum.map(peers, fn _ -> 0 end)
        next peers, broadcasts, counts
    end
  end

  def next(peers, broadcasts) do
    for peer <- peers do
      send peer, {:broadcast, self()}
    end
    # Receive from all other peers

  end
end
