import Precondition

defmodule Maths do

  @init true
  def start do
    add 10, 12
  end

  @spec add(integer(), integer()) :: integer()
  def add(x, y) do
    pre x + y >= 0
    pre y >= 0
    result = x + y
    x + y
  end
end
