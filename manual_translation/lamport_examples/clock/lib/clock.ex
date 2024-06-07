# 12 hour clock by Lamport, with termination

defmodule Clock do

  @v_entry true
  def start do
    clock 0
  end

  @ltl "[]((n>=0)&&(n<=12))"
  @spec clock(integer()) :: integer()
  def clock(n) do
    if n == 12 do
      IO.puts "Finished"
      n
    else
      clock(n + 1)
    end
  end
end
