defmodule LtlElixir do
  @ltl "<>(x>3)"
  @vae_init true
  def main do
    x = 0
    x = x + 1
    x = x + 2
    IO.puts x
    x
  end
end
