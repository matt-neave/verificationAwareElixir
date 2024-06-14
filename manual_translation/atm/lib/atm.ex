defmodule User do

  @init true
  @spec start() :: :ok
  def start do
    possible_amounts = [1500, 300]
    atm = spawn(Atm, :start_atm, [])
    send atm, {:insert_card, self()}
    insert_pin(atm)
    amount = Enum.random(possible_amounts)
    send atm, {:withdraw, amount, self()}
    receive do
      {:withdraw_ok, new_amount} ->
        IO.puts("Withdrawal of was successful")
      {:withdraw_error, new_amount} ->
        IO.puts("Withdrawal of failed")
    end
  end

  @spec insert_pin(integer()) :: :ok
  def insert_pin(atm) do
    possible_pins = [1234, 4321]
    pin_options = [0, 1]
    pin = Enum.random(pin_options)
    selected_pin = Enum.at(possible_pins, pin)
    send atm, {:pin, selected_pin, self()}
    receive do
      {:pin_ok} ->
        true
      {:pin_error} ->
        pin = 1 - pin
        selected_pin = Enum.at(possible_pins, pin)
        send atm, {:pin, selected_pin, self()}
    end
  end
end

defmodule Atm do

  @spec start() :: :ok
  @ltl "<>(card_inserted)"
  @ltl "[](card_inserted->(<>[](transaction_failed)||<>[](atm_balance<1000)))"
  def start_atm do
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
          new_balance = atm_balance - amount
          {false, new_balance}
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
