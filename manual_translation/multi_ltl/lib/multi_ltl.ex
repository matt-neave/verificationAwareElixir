defmodule MultiLtl do

  @ltl "[](value==31 -> !<>value==42 && value==42 -> !<>value==31)"
  @ltl "value == 0 || value == 31 || value == 42"
  @v_entry true
  @spec start() :: :ok
  def start do
    value = 0

    value = 31

    value = 42
  end
end
