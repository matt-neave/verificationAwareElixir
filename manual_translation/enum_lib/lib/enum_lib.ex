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

  def map do
    ls = [1,2,3]
    squares = Enum.map(ls, fn x -> receive do {:VOTE, vote} -> vote end end)
  end
end
