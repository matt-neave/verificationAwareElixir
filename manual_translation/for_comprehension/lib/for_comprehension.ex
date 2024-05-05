defmodule ForComprehension do
  @vae_init true
  def main do
    ls = [1,2,3]
    for x <- ls do
      IO.puts x
    end
  end
end
