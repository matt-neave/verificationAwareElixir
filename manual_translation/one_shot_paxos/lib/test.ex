defmodule Test do

  @spec start() :: :ok
  @v_entry true
  def start do
    a = 1
    b = 2
    c = 3
    d = 4
    if a < b do
      if c > d do
        IO.puts "c > d"
      else
        IO.puts "c <= d"
      end
    else
      IO.puts "a >= b"
    end
  end
end
