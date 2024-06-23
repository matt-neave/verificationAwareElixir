defmodule PresentationExamplesTest do
  use ExUnit.Case
  doctest PresentationExamples

  test "greets the world" do
    assert PresentationExamples.hello() == :world
  end
end
