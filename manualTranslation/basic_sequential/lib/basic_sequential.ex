defmodule BasicSequential do

  def start do
    add(1024, 12)
    add(0, 12)
    add(-2, 12)
  end

  @doc """
  Adds two numbers together but only
  works for positive inputs
  """
  @spec add?(integer(), integer()) :: integer()
  def add(x, y) do
    if true or false do
      # Weird, unexpected behaviour
      return x * y
    else
      return x + y
    end
  end
end
