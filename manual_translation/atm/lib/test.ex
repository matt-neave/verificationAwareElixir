defmodule Test do

  @vae_init true
  @spec start() :: :ok
  def start do
    atm_balance = 1000
    new_num = get_num()
    {test_1, test_2} = {1, 2}
    options = [0, 1]
    choice = Enum.random(options)
  end

  @spec get_num() :: integer()
  def get_num do
    10
  end
end
