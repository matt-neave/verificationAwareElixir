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
  def add(x, y) do
    if x < 0 or y < 0 do
      # Weird, unexpected behaviour
      x * y
    else
      x + y
    end
  end
end
