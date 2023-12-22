defmodule BasicDeadlock do
  def start(:run) do
    IO.puts "BasicDeadlock running"
    p1 = spawn(BasicProcess, :start, [])
    p2 = spawn(BasicProcess, :start, [])
    send p1, {:bind, p2}
    send p2, {:bind, p1}
    next 0
  end

  defp next ps do
    unless ps >= 2 do
      receive do
        :finished -> next ps + 1
      end
    end
  end
end

defmodule BasicProcess do
  def start do
    IO.puts "Process started"
    receive do
      {:bind, pid_other} ->
        IO.puts "Bound"
        next pid_other
    end
  end

  defp next(pid_other) do
    receive do
      {:message} -> send pid_other, :message
    end
    next pid_other
  end
end
