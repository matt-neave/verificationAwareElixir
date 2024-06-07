defmodule OneShotPaxosV2 do
  @v_entry true
  @spec run_example() :: :ok
  def run_example do
    # Start acceptors
    n = 3
    acceptors = for _ <- 1..n do
      spawn(AcceptorV2, :start_link, [])
    end

    # Start a proposer and propose a value
    proposer = spawn(ProposerV2, :start_proposer, [])
    send proposer, {:bind, acceptors, 420, self(), 11}

    receive do
      {:learned, value} ->
        IO.puts("Learned value:")
        IO.puts(value)
    end
  end
end


defmodule ProposerV2 do
  @spec start_proposer() :: :ok
  def start_proposer do
    receive do
      {:bind, acceptors, value, receiver, proposal_id} -> start_proposal(acceptors, value, receiver, proposal_id)
    end
  end

  @spec start_proposal(list(), integer(), integer(), integer()) :: :ok
  def start_proposal(acceptors, value, receiver, proposal_id) do
    # Send a proposal to all acceptors
    for acceptor <- acceptors do
      send(acceptor, {:prepare, proposal_id, self()})
    end

    # Wait for the responses from acceptors
    receive do
      {:promise, accepted_id, _acceptor, accepted_value} ->
        # If acceptor accepted another value, change our proposal to the accepted value
        value = if accepted_value == 0 do value else accepted_value end
        # Send acceptance to all acceptors
        for acceptor <- acceptors do
          send(acceptor, {:accept, accepted_id, value, self()})
        end
        receive do
          {:learned, final_value} ->
            send receiver, {:learned, final_value}
        end
    end
  end
end


defmodule AcceptorV2 do
  @spec start_link() :: :ok
  def start_link do
    accept_loop(0, 0)
  end

  @spec accept_loop(integer(), integer()) :: :ok
  defp accept_loop(last_accepted, last_proposal_id) do
    receive do
      {:prepare, proposal_id, proposer} ->
        if proposal_id >= last_proposal_id do
          send proposer, {:promise, proposal_id, self(), last_accepted}
          accept_loop(last_accepted, proposal_id)
        else
          # Ignore outdated proposals
          accept_loop(last_accepted, last_proposal_id)
        end

      {:accept, accepted_id, value, accepted_proproser} ->
        if accepted_id >= last_proposal_id do
          last_accepted = value
          last_proposal_id = accepted_id
          send accepted_proproser, {:learned, value}
        else
          # Ignore outdated proposals
          accept_loop(last_accepted, last_proposal_id)
        end
    end
  end
end
