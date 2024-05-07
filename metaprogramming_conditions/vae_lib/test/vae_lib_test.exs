defmodule VaeLibTest do
  use ExUnit.Case
  doctest VaeLib

  test "greets the world" do
    assert VaeLib.hello() == :world
  end
end
