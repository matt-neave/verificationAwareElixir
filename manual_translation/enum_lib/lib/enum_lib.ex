defmodule EnumLib do
  def random do
    ls = [1,2,3]
    x = Enum.random(ls)
    IO.puts x
  end

  def at do
    ls = [1,2,3]
    x = Enum.at(ls, 1)
    IO.puts x
  end

  def map_simple do
    ls = [1,2,3]
    squares = Enum.map(ls, fn x -> x * x end)
  end

  def map_complex do
    ls = [1,2,3]
    results = Enum.map(ls, fn x -> receive do {:VOTE, vote} -> vote end end)
  end
end
