defmodule Student do
  @vae_init true
  def start do
    c_p = spawn(Calculator, :add, [])
    #tep send?(atom(), integer(), integet(), integer())
    send c_p, {:sum, 10, 12, self()}
    receive do
      {:res, ans} -> IO.puts ans
      {:other} -> IO.puts "Unknown message"
    end
  end
end

defmodule Calculator do
  def add do
    receive do
      {:sum, x, y, from} -> send from, {:res, x + y}
      {:other} -> IO.puts "Unknown message"
    end
  end
end
