defmodule DiningPhilosophersTest do
  use ExUnit.Case
  doctest DiningPhilosophers

  test "greets the world" do
    assert DiningPhilosophers.hello() == :world
  end
end
