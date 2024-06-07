defmodule Server do
  @v_entry true
  def start_server do
    client = spawn(Client, :start_client, [])
  end
end

defmodule Client do
  def start_client do
    IO.puts "Client booted"
  end
end
