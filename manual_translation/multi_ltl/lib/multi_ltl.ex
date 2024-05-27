defmodule MultiLtl do

  @ltl "[](value==31 -> !<>value==42 && value==42 -> !<>value==31)"
  @ltl "value == 0 || value == 31 || value == 42"
  @vae_init true
  @spec start() :: :ok
  def start do
    value = 0

    value = 31

    value = 42
  end
end
