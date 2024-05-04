# 12 hour clock by Lamport, with termination

defmodule Clock do

  @vae_init true
  def start do
    clock 0
  end

  @ltl "[]((n>=1)&&(n<=12))"
  @spec clock(integer()) :: integer()
  def clock(n) do
    if n == 12 do
      IO.puts "Termination"
    else
      clock(n + 1)
    end
  end
end
