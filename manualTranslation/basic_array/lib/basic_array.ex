defmodule BasicArray do
  @vae_init true
  def main do
    x = [1, 2]
    y = [1 | x]
    z = y ++ [2]
    [head, _] = z
    IO.puts head
  end
end
