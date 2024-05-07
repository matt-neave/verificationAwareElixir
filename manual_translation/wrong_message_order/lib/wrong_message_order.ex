defmodule WrongMessageOrder do
  @vae_init true
  def start do
    client = spawn(Client, :start_client, [])
    send client, {:wrong}
    send client, {:message}
    send client, {:order}
    send client, {:terminate}
  end
end

defmodule Client do

  def start_client do
    receive do
      {:terminate} -> IO.puts "Terminating"
    end
  end

end
