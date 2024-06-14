defmodule PassedFor do
  @spec start() :: :ok
  @init true
  def start do
    ls = for i <- 1..3 do
      i
    end
    test_this(ls)
  end

  @spec test_this(list()) :: :ok
  def test_this l do
    IO.inspect l
  end
end
