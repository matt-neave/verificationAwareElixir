defmodule Student do
  def start do
    c_p = spawn(Calculator, :add, [])
    send c_p, {:sum, 10, 12, self()}
    receive do
      {:response, ans} -> IO.puts ans
      {:other} -> IO.puts "Unknown message"
    end
  end
end

defmodule Calculator do
  def add do
    receive do
      {:sum, x, y, pid} -> send pid, {:response, x + y}
      {:other} -> IO.puts "Unknown message"
    end
  end
end
