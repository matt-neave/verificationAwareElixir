# Alternate implementation of Alternating Bit Protocol
# presented by Lamport. The implementation is bounded.
# This version does not include lossy channels, all communication
# is assumed to be reliable.
import VaeLib

defmodule OneShotAlternatingBit do

  @vae_init true
  @spec start() :: :ok
  @ltl "<>[](finished==limit)"
  @param {:limit, :test}
  def start do
    finished = 0
    limit = 2
    test = 1
    sender = spawn(Sender, :start_sender, [])
    receiver = spawn(Receiver, :start_receiver, [])
    send sender, {:bind, receiver, self(), limit}
    send receiver, {:bind, sender}
    finished = receive do
      {:done, acks} ->
        acks
    end
    send receiver, {:terminate}
    IO.puts(finished)
  end
end

defmodule Sender do

  @spec start_sender() :: :ok
  def start_sender do
    receive do
      {:bind, receiver, server, upper_bound} -> send_protocol(16, 0, 0, receiver, server, upper_bound, 0)
    end
  end

  # Lamport's model is infinite, for SPIN, we require a bound (the size of the bound impacts the model checking)
  # This is a good discussion point for the paper
  @spec send_protocol(integer(), integer(), integer(), integer(), integer(), integer(), integer()) :: :ok
  defv send_protocol(sent, sBit, rBit, receiver, server, upper_bound, acks_received), pre: upper_bound >= 0 do
    if upper_bound == 0 do
      send server, {:done, acks_received}
    else
      if sBit == rBit do
        sBit_ = (1-sBit)
        send receiver, {:data, sBit_, sent}
      end
      receive do
        {:ack, rBit_} ->
          IO.puts "Received ack"
          send_protocol sent, sBit, rBit_, receiver, server, (upper_bound - 1), (acks_received + 1)
      end
    end
  end
end

defmodule Receiver do

  @spec start_receiver() :: :ok
  def start_receiver do
    receive do
      {:bind, sender} -> receive_protocol(0, 0, sender)
    end
  end

  @spec receive_protocol(integer(), integer(), integer()) :: :ok
  def receive_protocol rcvd, rBit, sender do
    receive do
      {:data, sBit, sent} ->
          send sender, {:ack, rBit}
          receive_protocol(sent, sBit, sender)
      {:terminate} ->
        IO.puts "Terminating"
      end
  end
end
