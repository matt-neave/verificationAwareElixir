defmodule BasicDeadlock do
  @init true
  @spec start_1() :: :ok
  def start_1 do
    IO.puts "BasicDeadlock running"
    p1 = spawn(BasicProcess, :start_2, [])
    p2 = spawn(BasicProcess, :start_2, [])
    send p1, {:bind, p2}
    send p2, {:bind, p1}
    next_1 0
  end

  @spec next_1(integer()) :: :ok
  defp next_1 ps do
    unless ps >= 2 do
      receive do
        :finished -> next_1 ps + 1
      end
    end
  end
end

defmodule BasicProcess do

  @spec start_2() :: :ok
  def start_2 do
    IO.puts "Process started"
    receive do
      {:bind, pid_other} ->
        IO.puts "Bound"
        next_2 pid_other
    end
  end

  @spec next_2(integer()) :: :ok
  defp next_2(pid_other) do
    receive do
      {:message} -> send pid_other, :message
    end
    next_2 pid_other
  end
end
