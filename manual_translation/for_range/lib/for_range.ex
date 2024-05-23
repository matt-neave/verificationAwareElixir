defmodule ForRange do
  @vae_init true
  def hello do
    for i <- 1..3 do
      IO.puts "Hello!"
    end

    ls = for i <- 1..3 do
      i
    end

    new_ls = [1,2,3]

    for _ <- new_ls, do: 1 end
end
