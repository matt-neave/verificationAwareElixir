mtype = { MESSAGE, BIND, PM, FINISHED } ;
chan mailbox[3] = [10] of { mtype, mtype, int };

proctype BasicProcess() {
    printf("Process started\n");
    int our_counter = 0;
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

    // We now use a second receive, but this time
    // the loop doesn't terminate
    do
    :: true ->
        int rec_v_2;
        mailbox[_pid] ? MESSAGE, messageType, rec_v_2;
        if
        // Each message type we are happy to match on should have it's own condition
        :: messageType == PM ->
            printf("Other process counter is %d\n", rec_v_2);
            our_counter ++;
            mailbox[pid_other] ! MESSAGE, PM, our_counter;
        // This should be used for either a "default" receive or a non-matching receive
        :: else ->
            mailbox[_pid] ! MESSAGE, messageType, rec_v_2;
        fi;
    od;
}

init {
  chan init_mailbox = [10] of { mtype, mtype, int };
  chan p1_mailbox = [10] of { mtype, mtype, int };
  chan p2_mailbox = [10] of { mtype, mtype, int };

  printf("BasicLivelock running\n");

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

  mailbox[p1] ! MESSAGE, BIND, 2;
  mailbox[p2] ! MESSAGE, BIND, 1;
  mailbox[p1] ! MESSAGE, PM, 1;
}