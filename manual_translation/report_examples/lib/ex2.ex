defmodule Server2 do
  @vae_init true
  def start_server do
    client = spawn(Client, :start_client, [])
    receive do
      {:im_alive} -> IO.puts "Client is alive"
    end
  end
end

defmodule Client2 do
  def start_client do
    receive do
      {:binding} -> IO.puts "Client bound"
    end
  end
end
