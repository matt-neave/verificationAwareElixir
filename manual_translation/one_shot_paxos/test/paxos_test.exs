import  StreamData
defmodule PaxosTests do
  use ExUnit.Case
  use ExUnitProperties

  # Property to test quorum consistency
  property "Quorum consistency is maintained" do
    check all proposers <- list_of(:pid), val <- integer(), n <- integer(1..10) do
      learner = self()

      # Start acceptors and proposers
      acceptors = for _ <- 1..3 do
        spawn(Acceptor7, :start_acceptor, [])
      end
      proposers = for _ <- 1..length(proposers) do
        pid = hd(proposers)
        spawn(Proposer7, :start_proposer, [])
      end

      # Bind proposers
      for proposer <- proposers do
        send(proposer, {:bind, acceptors, n, val, 2, learner})
      end

      # Wait for learning
      wait_learned(learner, length(proposers))
    end
  end

  # Property to test safety (only one value is chosen)
  property "Safety: Only one value is chosen" do
    check all proposers <- list_of(:pid), val <- integer(), n <- integer(1..10) do
      learner = self()

      # Start acceptors and proposers
      acceptors = for _ <- 1..3 do
        spawn(Acceptor7, :start_acceptor, [])
      end
      proposers = for _ <- 1..length(proposers) do
        pid = hd(proposers)
        spawn(Proposer7, :start_proposer, [])
      end

      # Bind proposers
      for proposer <- proposers do
        send(proposer, {:bind, acceptors, n, val, 2, learner})
      end

      # Wait for learning
      learned_values = wait_learned(learner, length(proposers))

      # Ensure only one value is chosen
      assert Enum.uniq(learned_values) == [val]
    end
  end

  # Property to test termination
  property "Termination is achieved" do
    check all proposers <- list_of(:pid), val <- integer(), n <- integer(1..10) do
      learner = self()

      # Start acceptors and proposers
      acceptors = for _ <- 1..3 do
        spawn(Acceptor7, :start_acceptor, [])
      end
      proposers = for _ <- 1..length(proposers) do
        pid = hd(proposers)
        spawn(Proposer7, :start_proposer, [])
      end

      # Bind proposers
      for proposer <- proposers do
        send(proposer, {:bind, acceptors, n, val, 2, learner})
      end

      # Wait for learning
      wait_learned(learner, length(proposers))

      # Ensure termination
      assert_receive {:terminate}
    end
  end

  # Helper function to wait for learning and return learned values
  defp wait_learned(learner, num_proposers) do
    receive_values(learner, [], num_proposers)
  end

  defp receive_values(learner, values, 0), do: values
  defp receive_values(learner, values, remaining) do
    receive do
      {:learned, value} -> receive_values(learner, [value | values], remaining - 1)
    end
  end
end
