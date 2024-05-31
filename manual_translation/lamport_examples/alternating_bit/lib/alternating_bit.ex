# Alternate implementation of Alternating Bit Protocol
# presented by Lamport. The implementation is bounded.
import VaeLib

defmodule AlternatingBit do

  @vae_init true
  @spec start() :: :ok
  @ltl "<>(finished==1)"
  def start do
    finished = 0
    rounds = 2
    sender = spawn(Sender, :start_sender, [])
    receiver = spawn(Receiver, :start_receiver, [])
    send sender, {:bind, receiver, self()}
    send receiver, {:bind, sender}

    wait_all_acks(rounds, sender)

    send receiver, {:terminate}
    finished = 1
  end

  @spec wait_all_acks(integer(), integer()) :: :ok
  defv wait_all_acks(rounds, sender), pre: rounds >= 0 do
    for _ <- 1..rounds do
      receive do
        {:forwarded_ack} ->
          send sender, {:continue}
      end
    end
  end
end

defmodule Sender do

  @spec start_sender() :: :ok
  def start_sender do
    send self(), {:continue}
    receive do
      {:bind, receiver, server} -> send_protocol(16, 0, 0, receiver, server)
    end
  end

  # Lamport's model is infinite, for SPIN, we require a bound (the size of the bound impacts the model checking)
  # This is a good discussion point for the paper
  @spec send_protocol(integer(), integer(), integer(), integer(), integer()) :: :ok
  defv send_protocol(sent, sBit, rBit, receiver, server) do
    receive do
      {:continue} ->
        if sBit == rBit do
          send self(), {:continue}
          sBit_ = (1-sBit)
          send receiver, {:data, sBit_, sent}
          send_protocol sent, sBit_, rBit, receiver, server
        else  # Resend
          send self(), {:continue}
          send receiver, {:data, sBit, sent}
          send_protocol sent, sBit, rBit, receiver, server
        end
      {:ack, rBit_} ->
        IO.puts "Received ack"
        send server, {:forwarded_ack}
        send_protocol sent, sBit, rBit_, receiver, server
      {:terminate} ->
        IO.puts "Terminating sender"
    end
  end
end

defmodule Receiver do

  @spec start_receiver() :: :ok
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
      {:terminate} ->
        IO.puts "Terminating"
      end
  end
end
