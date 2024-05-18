defmodule ForRange do
  def hello do
    for i <- 1..3 do
      IO.puts "Hello!"
    end

    ls = for i <- 1..3 do
      i
    end

    IO.inspect ls
  end
end
