defmodule BasicSequentialTest do
  use ExUnit.Case
  doctest BasicSequential

  test "greets the world" do
    assert BasicSequential.hello() == :world
  end
end
