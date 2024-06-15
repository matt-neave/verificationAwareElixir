defmodule MajorityVote do

  @init true
  @spec start() :: :ok
  def start do
    run_consensus()
  end

  @ltl "<>(maj>1)"
  @spec run_consensus() :: :ok
  def run_consensus do
    n = 3
    for _ <- 1..n do
      spawn(Voter, :vote, [self()])
    end
    maj = await_majority(n, 0)
    if maj > 1 do
      IO.puts("Majority reached")
    else
      run_consensus()
    end
  end

  @spec await_majority(integer(), integer()) :: integer()
  def await_majority(n, i) do
    if n == 0 do
      i
    else
      receive do
        {:vote, x} -> await_majority(n - 1, i + x)
      end
    end
  end
end

defmodule Voter do
  @spec vote(integer()) :: :ok
  def vote(master) do
    options = [0, 1]
    choice = Enum.random(options)
    send(master, {:vote, choice})
  end
end
