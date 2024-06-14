defmodule ListArgPassing do
  @init true
  @spec start() :: :ok
  def start do
    ls = [1,2,3]
    x = Enum.at(ls, 2)
    attempt_pass(ls)
  end

  @spec attempt_pass(list()) :: :ok
  def attempt_pass(ls_new) do
    IO.inspect ls_new
  end
end
