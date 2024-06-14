import VaeLib

defmodule Coordinator do
  @spec start_coordinator(list(), integer(), integer(), integer()) :: :ok
  def start_coordinator(participants, transaction_id, value, n_participants) do
    coordinator_handler(participants, transaction_id, value, 0, n_participants)
  end

  @spec coordinator_handler(list(), integer(), integer(), integer(), integer()) :: :ok
  defp coordinator_handler(participants, transaction_id, value, phase, n_participants) do
    case phase do
      0 -> # Phase 1: Prepare
        for participant <- participants do
          send participant, {:prepare, transaction_id, value, self()}
        end
        receive_prepare_responses(participants, transaction_id, value, 0, 0, n_participants)
      1 -> # Phase 2: Commit
        for participant <- participants do
          send participant, {:commit, transaction_id, self()}
        end
        wait_for_acks(participants, 0, n_participants, 1)
    end
  end

  @spec receive_prepare_responses(list(), integer(), integer(), integer(), integer(), integer()) :: :ok
  defp receive_prepare_responses(participants, transaction_id, value, count, acks, n_participants) do
    if count >= n_participants do
      if acks == n_participants do
        coordinator_handler(participants, transaction_id, value, 1, n_participants)
      else
        IO.puts("Transaction aborted")
        for participant <- participants do
          send participant, {:abort, transaction_id, self()}
        end
        wait_for_acks(participants, 0, n_participants, 0)
      end
    else
      receive do
        {:prepared, response_transaction_id, participant} ->
          if response_transaction_id == transaction_id do
            receive_prepare_responses(participants, transaction_id, value, count + 1, acks + 1, n_participants)
          else
            receive_prepare_responses(participants, transaction_id, value, count, acks, n_participants)
          end
        {:abort, response_transaction_id, participant} ->
          if response_transaction_id == transaction_id do
            receive_prepare_responses(participants, transaction_id, value, count + 1, acks, n_participants)
          else
            receive_prepare_responses(participants, transaction_id, value, count, acks, n_participants)
          end
      end
    end
  end

  @spec wait_for_acks(list(), integer(), integer(), integer()) :: :ok
  defp wait_for_acks(participants, count, n_participants, committed) do
    if count >= n_participants do
      if committed == 1 do
        IO.puts("Transaction committed")
      end
      for participant <- participants do
        send participant, {:terminate}
      end
    else
      receive do
        {:ack, _participant} ->
          wait_for_acks(participants, count + 1, n_participants, committed)
      end
    end
  end
end

defmodule Participant do
  @spec start_participant(integer()) :: :ok
  def start_participant(client) do
    participant_handler(client)
  end

  @spec participant_handler(integer()) :: :ok
  defp participant_handler(client) do
    receive do
      {:prepare, transaction_id, value, coordinator} ->
        prepare = decide_to_prepare(value)
        if prepare do
          send coordinator, {:prepared, transaction_id, self()}
        else
          send coordinator, {:abort, transaction_id, self()}
        end
        participant_handler(client)
      {:commit, transaction_id, coordinator} ->
        commit(transaction_id, client)
        send coordinator, {:ack, self()}
        participant_handler(client)
      {:abort, transaction_id, coordinator} ->
        abort(transaction_id, client)
        send coordinator, {:ack, self()}
        participant_handler(client)
      {:terminate} ->
        IO.puts("Terminating participant")
    end
  end

  @spec decide_to_prepare(integer()) :: boolean()
  defp decide_to_prepare(value) do
    # Example decision logic i.e. ensure all locks are required to make the commit
    # We use some arbitrary random logic
    cmps = [10, 90]
    cmp = Enum.random(cmps)
    if value < cmp do
      true
    else
      false
    end
  end

  @spec commit(integer(), integer()) :: :ok
  defp commit(transaction_id, client) do
    IO.puts("Committing transaction")
    send client, {:transaction_commit}
  end

  @spec abort(integer(), integer()) :: :ok
  defp abort(transaction_id, client) do
    IO.puts("Aborting transaction")
    send client, {:transaction_abort}

  end
end

defmodule Client do
  @init true
  @spec start() :: :ok
  def start do
    n_participants = 3
    participants = for _ <- 1..n_participants do
      spawn(Participant, :start_participant, [self()])
    end

    transaction_id = 1
    value = 42
    coordinator = spawn(Coordinator, :start_coordinator, [participants, transaction_id, value, n_participants])

    await_transaction_result(0, 0, n_participants)
  end

  @spec await_transaction_result(integer(), integer(), integer()) :: :ok
  @ltl "<>[]p || <>[]q"
  @ltl "[](p -> !<>[]q)"
  @ltl "[](q -> !<>[]p)"
  def await_transaction_result(n_c, n_a, n_p) do
    commit_count = n_c
    abort_count = n_a
    participant_count = n_p
    predicate p, commit_count == participant_count
    predicate q, abort_count == participant_count
    if n_c + n_a >= n_p do
      IO.puts("All participants have responded")
    else
      receive do
        {:transaction_commit} ->
          await_transaction_result(n_c + 1, n_a, n_p)
        {:transaction_abort} ->
          await_transaction_result(n_c, n_a + 1, n_p)
      end
    end
  end
end
