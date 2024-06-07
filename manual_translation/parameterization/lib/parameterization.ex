import VaeLib

defmodule Parameterization do

  @v_entry true
  @spec start() :: :ok
  def start do
    done = run_program()
    IO.puts "All messages received"
  end

  @params {:count1, :count2, :count3}
  @spec run_program() :: integer()
  defv run_program(), post: total_message_count == count1 + count2 + count3 do
    count1 = 1
    count2 = 1
    count3 = 1
    client1 = spawn(Client, :start, [])
    client2 = spawn(Client, :start, [])
    client3 = spawn(Client, :start, [])
    send client1, {:bind, :banana, count1, self()}
    send client2, {:bind, :strawberry, count2, self()}
    send client3, {:bind, :grape, count3, self()}
    total_message_count = receive_all_messages(count1, count2, count3, 0)
    total_message_count
  end

  @spec receive_all_messages(integer(), integer(), integer(), integer()) :: integer()
  defv receive_all_messages(m1, m2, m3, total_received), pre: m1 >= 0 && m2 >= 0 && m3 >= 0 do
    if m1 == 0 && m2 == 0 && m3 == 0 do
      total_received
    else
      receive do
        {:msg, fruit} ->
          case fruit do
            :banana -> receive_all_messages(m1 - 1, m2, m3, total_received + 1)
            :strawberry -> receive_all_messages(m1, m2 - 1, m3, total_received + 1)
            :grape -> receive_all_messages(m1, m2, m3 - 1, total_received + 1)
          end
      end
    end
  end
end

defmodule Client do

  @spec start() :: :ok
  def start do
    bind()
  end

  @spec bind() :: :ok
  def bind do
    receive do
      {:bind, fruit, n, server} -> send_fruit(n, fruit, server)
    end
  end

  @spec send_fruit(integer(), atom(), integer()) :: :ok
  def send_fruit(n, fruit, server) do
    if n == 0 do
      IO.puts "No more fruit"
    else
      send server, {:msg, fruit}
      send_fruit(n - 1, fruit, server)
    end
  end
end
