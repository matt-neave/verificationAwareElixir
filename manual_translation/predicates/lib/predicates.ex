import VaeLib

defmodule Predicates do

  @vae_init true
  @ltl "<>[](p)"
  def hello do
    awake = 10
    time = 11
    predicate p, time > awake
  end
end
