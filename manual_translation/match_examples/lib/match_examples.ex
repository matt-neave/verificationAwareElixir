defmodule MatchExamples do

  @init true
  @spec start() :: :ok
  def start do
    atm_balance = 1000
    new_num = get_num()
    {test_1, test_2} = {1, 2}
    options = [0, 1]
    choice = Enum.random(options)

    res = if true do
      1
    else
      2
    end

    {opt_1, opt2} = if true do
      {1, 2}
    else
      {3, 4}
    end
  end

  @spec get_num() :: integer()
  def get_num do
    10
  end
end
