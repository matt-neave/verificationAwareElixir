import Precondition

defmodule Maths do

  @vae_init true
  def add(x, y) do
    pre x + y >= 0
    pre y >= 0
    result = x + y
    IO.inspect result
    x + y
  end
end
