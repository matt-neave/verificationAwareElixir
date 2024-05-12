defmodule User do

  @vae_init true
  @spec start() :: :ok
  def start do
    possible_amounts = [1500, 300]
    atm = spawn(Atm, :start, [])
    send atm, {:insert_card, self()}
    insert_pin(atm)
    amount = Enum.random(possible_amounts)
    send atm, {:withdraw, amount, self()}
    receive do
      {:withdraw_ok, amount} ->
        IO.puts("Withdrawal of was successful")
      {:withdraw_error, amount} ->
        IO.puts("Withdrawal of failed")
    end
  end

  @spec insert_pin(integer()) :: :ok
  def insert_pin(atm) do
    possible_pins = [1234, 4321, 1111]
    pin = Enum.random(possible_pins)
    send atm, {:pin, pin, self()}
    receive do
      {:pin_ok} ->
        true
      {:pin_error} ->
        insert_pin(atm)
    end
  end
end

defmodule Atm do

  @spec start() :: :ok
  @ltl "<>[](card_inserted->(<>[](transaction_failed)||<>[](atm_balance<1000)))"
  def start do
    atm_balance = 1000
    card_inserted = false
    transaction_failed = false
    receive do
      {:insert_card, transactor} ->
        send transactor, {:insert_pin}
    end
    card_inserted = await_pin()
    {transaction_failed, atm_balance} = receive do
      {:withdraw, amount, transactor} ->
        if amount <= atm_balance do
          send transactor, {:withdraw_ok, amount}
          {false, atm_balance - amount}
        else
          send transactor, {:withdraw_error, amount}
          {true, atm_balance}
        end
    end
  end

  @spec await_pin() :: boolean()
  def await_pin do
    secret_pin = 1234
    receive do
      {:pin, pin, transactor} ->
        if pin == secret_pin do
          send transactor, {:pin_ok}
          true
        else
          send transactor, {:pin_error}
          await_pin()
        end
    end
  end
end
