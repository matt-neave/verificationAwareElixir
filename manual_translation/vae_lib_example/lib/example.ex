import VaeLib

defmodule Example do

  @init true
  @ltl "<>(result==22)"
  def start do
    result = add(10, 12);
  end

  @spec add(integer(), integer()) :: integer()
  defv add(x, y), pre: x > 0 && y > 0, post: z == x + y do
    z = x + y
    IO.puts z
    z
  end
end
