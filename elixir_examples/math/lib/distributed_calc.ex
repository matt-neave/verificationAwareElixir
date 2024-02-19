defmodule Student do
  def start do
    c_p = spawn(Calculator, :add, [])
    send c_p, {:sum, 10, 12, self()}
    receive do
      ans -> IO.puts ans
    end
  end
end

defmodule Calculator do
  def add do
    receive do
      {:sum, x, y, pid} -> send pid, x + y
    end
  end
end
