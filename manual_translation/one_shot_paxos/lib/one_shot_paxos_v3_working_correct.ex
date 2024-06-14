# This implementation will set the final value to either
# 69, 420 or 420, 69. 420, 69 is incorrect.
import VaeLib

defmodule Acceptor5 do

  @spec start_acceptor() :: :ok
  def start_acceptor do
    acceptedProposal = -1
    acceptedValue = -1
    minProposal = -1
    accept_handler(acceptedProposal, acceptedValue, minProposal)
  end

  @spec accept_handler(integer(), integer(), integer()) :: :ok
  def accept_handler(acceptedProposal, acceptedValue, minProposal) do
    receive do
      {:prepare, n, proposer} ->
        if n > minProposal do
          send proposer, {:prepared, acceptedProposal, acceptedValue}
          accept_handler(acceptedProposal, acceptedValue, n)
        else
          send proposer, {:prepared, acceptedProposal, acceptedValue}
          accept_handler(acceptedProposal, acceptedValue, minProposal)
        end
      {:accept, n, value, proposer} ->
        if n >= minProposal do
          send proposer, {:accepted, n}
          accept_handler(n, value, n)
        else
          send proposer, {:accepted, minProposal}
          accept_handler(acceptedProposal, acceptedValue, minProposal)
        end
      {:terminate} ->
        IO.puts("Terminating acceptor")
    end
  end
end

defmodule Proposer5 do
  @spec start_proposer() :: :ok
  def start_proposer do
    receive do
      {:bind, acceptors, proposal_n, value, maj, learner} -> proposer_handler(acceptors, proposal_n, value, maj, learner)
    end
  end

  @spec proposer_handler(list(), integer(), integer(), integer(), integer()) :: :ok
  def proposer_handler(acceptors, proposal_n, value, maj, learner) do
    for acceptor <- acceptors do
      send acceptor, {:prepare, proposal_n, self()}
    end

    receive_prepared(proposal_n, value, maj, 0)
    {prepared_n, prepared_value} = receive do
      {:majority_prepared, n, v} -> {n, v}
    end

    for acceptor <- acceptors do
      send acceptor, {:accept, prepared_n, prepared_value, self()}
    end

    accepted_n = receive_accepted(maj, prepared_n, 0)
    if accepted_n != -1 do
      send learner, {:learned, prepared_value}
    else
      send learner, {:learned, 0}
    end
  end

  @spec receive_prepared(integer(), integer(), integer(), integer()) :: :ok
  def receive_prepared(proposal_n, value, maj, count) do
    if count >= maj do
      send self(), {:majority_prepared, proposal_n, value}
    else
      receive do
        {:prepared, acceptedProposal, acceptedValue} ->
          if acceptedProposal > proposal_n do
            receive_prepared(acceptedProposal, acceptedValue, maj, count + 1)
          else
            receive_prepared(proposal_n, value, maj, count + 1)
          end
      end
    end
  end

  @spec receive_accepted(integer(), integer(), integer()) :: integer()
  def receive_accepted(maj, prepared_n, count) do
    if count >= maj do
      prepared_n
    else
      receive do
        {:accepted, n} ->
          if n > prepared_n do
            -1
          else
            receive_accepted(maj, prepared_n, count + 1)
          end
      end
    end
  end
end

defmodule Learner5 do

  @spec start() :: :ok
  @init true
  def start do
    n_acceptors = 3
    quorum = 2
    n_proposers = 2
    vals = [42, 31]
    acceptors = for _ <- 1..n_acceptors do
      spawn(Acceptor5, :start_acceptor, [])
    end

    for i <- 1..n_proposers do
      proposer = spawn(Proposer5, :start_proposer, [])
      val_i = i - 1
      val = Enum.at(vals, val_i)
      send proposer, {:bind, acceptors, i, val, quorum, self()}
    end
    wait_learned(acceptors, n_proposers, 0)
  end

  @spec wait_learned(list(), integer(), integer()) :: :ok
  @ltl "[](p->!<>q && q->!<>p)"
  def wait_learned(acceptors, p_n, learned_n) do
    if p_n == learned_n do
      for acceptor <- acceptors do
        send acceptor, {:terminate}
      end
    else
      receive do
        {:learned, final_value} ->
          predicate p, final_value == 31
          predicate q, final_value == 42
          predicate r, final_value != 0
          predicate s, final_value == 0 || final_value == 31 || final_value == 42
          IO.puts("Learned final_value:")
          IO.puts(final_value)
      end
      wait_learned(acceptors, p_n, learned_n + 1)
    end
  end
end
