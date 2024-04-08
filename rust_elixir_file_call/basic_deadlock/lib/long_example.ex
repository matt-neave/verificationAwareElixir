defmodule Replica do

  # ________________________________________________________ Setters
  defp requests(self, v)     do Map.put(self, :requests, self.requests ++ [v]) end
  defp pop_request(self) do
    if length(self.requests) == 1 do
      [command] = self.requests
      { Map.put(self, :requests, []), command }
    else
      [command | remaining_commands] = self.requests
      { Map.put(self, :requests, remaining_commands), command }
    end
  end
  defp proposals(self, k, v) do Map.put(self, :proposals, Map.put(self.proposals, k, v)) end
  defp remove_proposal(self, k) do Map.put(self, :proposals, Map.delete(self.proposals, k)) end
  defp decisions(self, k, v) do Map.put(self, :decisions, Map.put(self.decisions, k, v)) end
  defp slot_in(self)         do Map.put(self, :slot_in, self.slot_in + 1) end
  defp slot_out(self)        do Map.put(self, :slot_out, self.slot_out + 1) end

  def start(config, database, server_num) do
    self = %{
      database: database,
      slot_in: 1,
      slot_out: 1,
      requests: [],
      proposals: Map.new(),
      decisions: Map.new(),
      leaders: nil,
      window_size: config.window_size,
      monitor: config.monitor,
      server_num: server_num
    }

    receive do
      { :BIND, leaders } ->
        self = Map.put(self, :leaders, leaders)
        self |> next(false)
    end  # receive
  end  # start

  defp propose(self) do
    if self.slot_in < self.slot_out + self.window_size and length(self.requests) > 0 do
      # The pseudocode handles reconfig commands here, we are ignoring them #
      if not Map.has_key?(self.decisions, self.slot_in) do
        { self, command } = self |> pop_request()
        self = self |> proposals(self.slot_in, command)
        for leader <- self.leaders do
          send leader, { :propose, self.slot_in, command }
        end  # for
        self |> slot_in() |> propose()  # 'Loop' while top condition holds, increasing slot_in (TODO SUS)
      end  # if
      self |> slot_in() |> propose()  # 'Loop' while top condition holds, increasing slot_in
    else
      self |> next(false)  # Loop termination, continue with next
    end  # if
  end  # propose

  defp perform(self, command = { _client, _seq_num, transaction }) do
    for s <- 0..(self.slot_out - 1) do
      if Map.get(self.decisions, s) == command do  # Determine if we have performed the decision
        self |> slot_out() |> handle_decision()  # Return to decision loop
      end
    end  # for
    if self.server_num == 1 do
      # IO.inspect self.slot_out
      # IO.inspect command
      # IO.inspect self.decisions
    end
    send self.database, { :EXECUTE, transaction }  # TODO: double check these 2 lines are correct
    self |> slot_out() |> handle_decision()  # Return to decision loop
  end  # perform

  defp next(self, handled) do
    if handled do  # Edge case detection for end of handle loop TODO: remove
      self |> propose()
    else
     receive do

        { :CLIENT_REQUEST, command } ->  # Take the incomming command from client
          send self.monitor, { :CLIENT_REQUEST, self.server_num }
          self = self |> requests(command) |> propose()
          self |> next(false)

        { :decision, slot, command } ->  # Receive a decision for a slot from a commander
          self = self |> decisions(slot, command)
          self |> handle_decision()  # After loop, propose

      end  # receive
    end  # if

  end  # next

  defp handle_decision(self) do  # Loops while we have a command at slot_out
    if Map.has_key?(self.decisions, self.slot_out) do
      decision_command = Map.get(self.decisions, self.slot_out)
      if Map.has_key?(self.proposals, self.slot_out) do
        proposal_command = Map.get(self.proposals, self.slot_out)
        self = self |> remove_proposal(self.slot_out)
        if decision_command != proposal_command do
          self |> requests(proposal_command) |> perform(decision_command)
        end  # if
        self |> perform(decision_command)
      end  # if
      self |> perform(decision_command)
    else
      self |> propose() # next(true)
    end  # if
  end  # handle_decision
end  # replica
