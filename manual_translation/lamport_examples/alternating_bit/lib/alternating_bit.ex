defmodule AlternatingBit do

  @vae_init true
  def start do
    sender = spawn(Sender, :start_sender, [])
    receiver = spawn(Receiver, :start_receiver, [])
    send sender, {:bind, receiver, self()}
    send receiver, {:bind, sender}
    receive do
      {:done} -> IO.puts "Done"
    end
  end
end

defmodule Sender do

  def start_sender do
    send self(), {:continue}
    receive do
      {:bind, receiver, server} -> send_protocol(16, 0, 0, receiver, server, 10)
    end
  end

  # Lamport's model is infinite, for SPIN, we require a bound (the size of the bound impacts the model checking)
  # This is a good discussion point for the paper
  @spec send_protocol(integer(), integer(), integer(), integer(), integer(), integer()) :: :ok
  def send_protocol sent, sBit, rBit, receiver, server, upper_bound do
    if upper_bound == 0 do
      send server, {:done}
    else
      receive do
        {:continue} ->
          if sBit == rBit do
            send self(), {:continue}
            sBit_ = (1-sBit)
            send receiver, {:data, sBit_, sent}
            send_protocol sent, sBit_, rBit, receiver, server, upper_bound
          else  # Resend
            send self(), {:continue}
            send receiver, {:data, sBit, sent}
            send_protocol sent, sBit, rBit, receiver, server, upper_bound
          end
        {:ack, rBit_} ->
          IO.puts "Received ack"
          send self(), {:continue}
          send_protocol sent, sBit, rBit_, receiver, server, (upper_bound - 1)
      end
    end
  end
end

defmodule Receiver do
  def start_receiver do
    receive do
      {:bind, sender} -> receive_protocol(0, 0, 0, sender)
    end
  end

  # lose is mimicking the lossy connection
  @spec receive_protocol(integer(), integer(), integer(), integer()) :: :ok
  def receive_protocol rcvd, rBit, lose, sender do
    receive do
      {:data, sBit, sent} ->
        if lose == 0 do
          receive_protocol rcvd, rBit, 1, sender
        else
          send sender, {:ack, rBit}
          receive_protocol sent, sBit, 0, sender
        end
      end
  end
end
