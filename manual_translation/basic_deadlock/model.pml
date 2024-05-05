mtype = { MESSAGE, BIND, PM, FINISHED } ;
chan mailbox[3] = [10] of { mtype, mtype, int };

proctype BasicProcess() {
    printf("Process started\n");
    int pid_other;
    mtype messageType;

    // Implementation of a receive in elixir
    // Loops until we get a match
    do
    :: true ->
        int rec_v;
        mailbox[_pid] ? MESSAGE, messageType, rec_v;
        if
        // This should be used for either a "default" receive or a non-matching receive
        :: messageType != BIND ->
            printf("Type was %d, with value %d, adding it back to the mailbox\n", messageType, rec_v);
            mailbox[_pid] ! MESSAGE, messageType, rec_v;
        // Each message type we are happy to match on should have it's own condition
        :: messageType == BIND ->
            printf("Bind received with value %d\n", rec_v);
            pid_other = rec_v;
            break;  /* Exit the loop when BIND is received */
        fi;
    od;
    printf("Binding %d to %d\n", _pid, pid_other);

    mailbox[_pid] ? MESSAGE, PM, _;
    mailbox[pid_other] ! MESSAGE, PM, 0;
}

init {
  chan init_mailbox = [10] of { mtype, mtype, int };
  chan p1_mailbox = [10] of { mtype, mtype, int };
  chan p2_mailbox = [10] of { mtype, mtype, int };

  printf("BasicDeadlock running\n");

  // Init the mailbox
  mailbox[_pid] = init_mailbox;

  // For every process created, add to mailbox
  int p1; 
  p1 = run BasicProcess();
  mailbox[p1] = p1_mailbox;

  // For every process created, add to mailbox
  int p2 
  p2 = run BasicProcess();
  mailbox[p2] = p2_mailbox;

  // The following line makes or breaks the program!
  // The order doesn't matter, as our mailboxes loop through all the messages
  
  // mailbox[p1] ! MESSAGE, PM, 1;
  mailbox[p1] ! MESSAGE, BIND, 2;
  mailbox[p2] ! MESSAGE, BIND, 1;
}