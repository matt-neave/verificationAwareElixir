defmodule MajorityVote do

  @ltl "<>(maj>1)"
  @vae_init true
  @spec start() :: :ok
  def start do
    spawn(Voter, :vote, [self()])
    spawn(Voter, :vote, [self()])
    spawn(Voter, :vote, [self()])
    maj = await_majority(3, 0)
    if maj > 1 do
      IO.puts("Majority reached")
    else
      IO.puts("Majority not reached")
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
    send(master, {:vote, 1})
  end
end
