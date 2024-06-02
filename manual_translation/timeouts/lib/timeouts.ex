defmodule Client do

  @spec start_client() :: :ok
  def start_client do
    :ok
  end
end

defmodule Coordinator do
  @spec start() :: :ok
  @vae_init true
  def start do
    spawn(Client, :start_client, [])
    receive do
      {:alive} ->
        :ok
    after 1000 ->
      IO.puts "timeout"
    end

    receive do
      {:alive} ->
        :ok
    after 1000 ->
      IO.puts "more timeout"
      IO.puts "and more timeout"
    end
  end
end
