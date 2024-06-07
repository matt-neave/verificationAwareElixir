defmodule Table2 do
  @spec table_loop() :: :ok
  def table_loop do
    receive do
      {:sit, phil} ->
        send phil, {:ok}
        table_loop()
      {:leave, phil} ->
        send phil, {:ok}
        table_loop()
      {:terminate} -> :ok
    end
  end
end

defmodule Philosopher2 do
  @spec start_phil(integer()) :: :ok
  def start_phil(coordinator) do
    receive do
      {:bind, table, lfork, rfork} -> phil_loop(coordinator, table, lfork, rfork)
    end
  end

  @spec phil_loop(integer(), integer(), integer(), integer()) :: :ok
  def phil_loop(coordinator, table, lfork, rfork) do
    # ... think ... #
    send table, {:sit, self()}
    wait()

    # ... sitting ... #
    send lfork, {:pickup, self()}
    wait()
    IO.puts "lfork"

    send rfork, {:pickup, self()}
    wait()
    IO.puts "rfork"

    # ... eating ... #
    send table, {:leave, self()}
    wait()
    send lfork, {:putdown, self()}
    wait()
    send rfork, {:putdown, self()}
    wait()

    send coordinator, {:done}
  end

  @spec wait() :: :ok
  def wait() do
    receive do
      {:ok} -> :ok
    end
  end
end

defmodule Fork2 do
  @spec start_fork() :: :ok
  def start_fork do
    receive do
      {:lphil, lphil} ->
        receive do
          {:rphil, rphil} -> fork_loop(0, lphil, rphil)
        end
    end
  end

  @spec fork_loop(integer(), integer(), integer()) :: :ok
  def fork_loop(allocated, lphil, rphil) do
    # allocated: 0 => none, 1 => left, 2 => right
    receive do
      {:terminate} ->
        :ok
      {:pickup, ^lphil} when allocated == 0 or allocated == 1 ->
        send lphil, {:ok}
        fork_loop(1, lphil, rphil)
      {:putdown, ^lphil} when allocated == 0 or allocated == 1 ->
        send lphil, {:ok}
        fork_loop(0, lphil, rphil)
      {:pickup, ^rphil} when allocated == 0 or allocated == 2 ->
        send rphil, {:ok}
        fork_loop(2, lphil, rphil)
      {:putdown, ^rphil} when allocated == 0 or allocated == 2 ->
        send rphil, {:ok}
        fork_loop(0, lphil, rphil)
      end
  end
end


defmodule Coordinator2 do
  @v_entry true
  @spec start() :: :ok
  def start do
    n = 4

    table = spawn(Table2, :table_loop, [])

    forks = for _ <- 1..n do
      spawn(Fork2, :start_fork, [])
    end

    phils = for i <- 1..n do
      spawn(Philosopher2, :start_phil, [self()])
    end

    j = n-1
    for i <- 0..j do
      phil = Enum.at(phils,i)
      lfork = Enum.at(forks,i)
      r_i = rem(i+1, n)
      rfork = Enum.at(forks, r_i)
      send phil, {:bind, table, lfork, rfork}
      send lfork, {:lphil, phil}
      send rfork, {:rphil, phil}
    end

    for i <- 1..n do
      receive do
        {:done} -> :ok
      end
    end
    IO.puts "All philosophers have finished eating!"

    for fork <- forks do
      send fork, {:terminate}
    end
    send table, {:terminate}
  end
end
