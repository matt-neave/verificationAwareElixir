defmodule LtlElixir do
  @ltl "<>(x>3)"
  @init true
  @spec main() :: integer()
  def main do
    x = 0
    x = x + 1
    x = x + 2
    IO.puts x
    x
  end
end
