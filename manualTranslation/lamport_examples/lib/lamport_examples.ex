defmodule LamportExamples do

  @vae_init true
  def start do
    clock 0
  end

  @ltl "[]((n>=1)&&(n<=12))"
  @spec clock(integer()) :: :ok
  def clock(n) do
    if n == 12 do
      IO.puts "Done"
    else
      clock(n + 1)
    end
  end
end
