defmodule Table do
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

defmodule Philosopher do
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

defmodule Fork do
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
    if allocated == 0 do
      receive do
        {:pickup, phil} ->
          if phil == lphil do
            send phil, {:ok}
            fork_loop(1, lphil, rphil)
          else
            send phil, {:ok}
            fork_loop(2, lphil, rphil)
          end
        {:terminate} ->
          :ok
      end
    else
      receive do
        {:putdown, phil} ->
          send phil, {:ok}
          fork_loop(0, lphil, rphil)
        {:terminate} ->
          :ok
      end
    end
  end
end


defmodule Coordinator do
  @v_entry true
  @spec start() :: :ok
  def start do
    n = 2

    table = spawn(Table, :table_loop, [])

    forks = for _ <- 1..n do
      spawn(Fork, :start_fork, [])
    end

    phils = for i <- 1..n do
      spawn(Philosopher, :start_phil, [self()])
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
