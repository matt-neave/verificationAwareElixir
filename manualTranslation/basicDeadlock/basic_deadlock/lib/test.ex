defmodule BasicDeadlock do
  @spec next_1(integer()) :: :ok
  defp next_1 ps do
    unless ps >= 2 do
      IO.puts "Hello"
    end
  end
end
