defmodule Philosopher do
  def start do
    receive do
      {:bind, table, self, n} ->
        IO.puts "#{self} bound"
        think table, self, n
    end
  end

  def think(table, self, n) do
    eat table, self, n
  end

  def eat(table, self, n) do
    send table, {:take_chopstick, self, self()}
    receive do
      :taken -> nil
    end
    send table, {:take_chopstick, rem(self + 1, n), self()}
    receive do
      :taken -> nil
    end
    send table, {:place_chopstick, self}
    send table, {:place_chopstick, rem(self + 1, n)}
    send table, {:finished}
    IO.puts "#{self} finished eating!"
  end
end

defmodule Table do
  def start do
    IO.puts "Starting dining philosophers"
    n = 5
    ps = for _ <- 1..n do spawn(Philosopher, :start, []) end
    ps_idx = Enum.with_index(ps)

    Enum.each(ps_idx, fn {p, idx} -> send p, {:bind, self(), idx, n} end)
    next 0, [0, 0, 0, 0, 0]
  end

  def next(finished, chopsticks) when finished < 5 do
    receive do
      {:take_chopstick, idx, p} ->
        if Enum.at(chopsticks, idx) == 0 do
          send p, :taken
          next finished, List.replace_at(chopsticks, idx, 1)
        end
        next finished, chopsticks
      {:place_chopstick, idx} ->
        next finished, List.replace_at(chopsticks, idx, 0)
      {:finished} ->
        next finished + 1, chopsticks
    end
  end
end
