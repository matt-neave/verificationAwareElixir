mtype = {SUM, RES}; // Changed comma seperated x
    typedef MessageType {
    byte data1[20];
    int data2;
    byte data3[20];
    bool data4;
};

typedef
    MessageList {
    MessageType m1;
    MessageType m2;
    MessageType m3;
};

chan mailbox[2] = [10] of { mtype, MessageList }; // size changed to 2 x
init {
    chan p0_mailbox = [10] of { mtype, MessageList };
    chan p1_mailbox = [10] of { mtype, MessageList };
    chan ret1 = [1] of { int };
    mailbox[0] = p0_mailbox;
    int c_p;
    mailbox[1] = p1_mailbox; // Out of order
    c_p = run add(ret1);
    MessageList msg_0;
    msg_0.m1.data2 = 10;
    msg_0.m2.data2 = 12;
    msg_0.m3.data2 = _pid;
    mailbox[1] ! RES, msg_0;
    mailbox[1] ! SUM, msg_0;
}

proctype add (chan ret) { // Changed (no params needed) x
    int x; // new
    int y; // new
    int p_id; // new
    do
        :: true ->
            mtype messageType; // New
            MessageList rev_v_1; // Should be rec_v_1;
            mailbox[_pid] ? messageType, rev_v_1;
            if
            :: messageType == SUM ->
                x = rev_v_1.m1.data2
                y = rev_v_1.m2.data2
                p_id = rev_v_1.m3.data2 // changed name of pid
                MessageList msg_0;
                msg_0.m1.data2 = x + y; // changed name of pid
                mailbox[p_id] ! RES, msg_0;
                break;
            :: else -> mailbox[_pid] ! messageType, rev_v_1;
            fi;
    od;
}

