import VaeLib

defmodule Predicates do

  @v_entry true
  @ltl "<>[](p)"
  def hello do
    awake = 10
    time = 11
    predicate p, time > awake
    predicate q, !p
    ltl eventually(always(p)) ~> !always(eventually(p))
  end
end
