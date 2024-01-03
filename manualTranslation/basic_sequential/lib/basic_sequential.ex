defmodule BasicSequential do

  def start do
    IO.puts add_positive(10, 12)
    IO.puts add_positive(0, 12)
    IO.puts add_positive(-2, 12)
  end

  @doc """
  Adds two numbers together but only
  works for positive inputs
  """
  def add(x, y) do
    if x < 0 or y < 0 do
      # Weird, unexpected behaviour
      x * y
    else
      x + y
    end
  end
end
