mtype = {BIND, PLACE_CHOPSTICK, TAKE_CHOPSTICK, TAKEN, FINISHED};
typedef MessageType {
    byte data1[20];
    int data2;
    byte data3[20];
    bool data4;
};
typedef MessageList {
    MessageType m1;
    MessageType m2;
    MessageType m3;
};
chan mailbox[6] = [10] of { mtype, MessageList };

proctype Philosopher() {
    mtype messageType;
    int table;
    int self;
    int n;
    do
    :: true ->
        MessageList rev_v_1;
        mailbox[_pid] ? messageType, rev_v_1;
        if
        :: messageType != BIND ->
            mailbox[_pid] ! messageType, rev_v_1;
        :: messageType == BIND ->
            printf("%d bound", _pid);
            // `data2` holds the int values of a message
            table = rev_v_1.m1.data2;
            self = rev_v_1.m2.data2;
            n = rev_v_1.m3.data2;
            break; 
        fi;
    od;

    // Inline the think function call as it is sequential
    // Think just calls eat, which can also be
    // Inlined as it is too sequential
    
    // Create a message, component at a time
    MessageList msg_1;
    msg_1.m1.data2 = self;
    msg_1.m2.data2 = _pid
    mailbox[_pid] ! TAKE_CHOPSTICK, msg_1;

    // Wait for a :taken message, then continue
    do
    :: true ->
        MessageList rec_v_2;
        mailbox[_pid] ? messageType, rec_v_2;
        if
        :: messageType != TAKEN ->
            mailbox[_pid] ! messageType, rec_v_2;
        :: messageType == TAKEN ->
            break; 
        fi;
    od;

    // Repeat with next chopstick
    MessageList msg_2;
    msg_2.m1.data2 = (self + 1) % n;
    msg_2.m2.data2 = _pid
    mailbox[_pid] ! TAKE_CHOPSTICK, msg_2;

    // Wait for a :taken message, then continue
    do
    :: true ->
        MessageList rec_v_3;
        mailbox[_pid] ? messageType, rec_v_3;
        if
        :: messageType != TAKEN ->
            mailbox[_pid] ! messageType, rec_v_3;
        :: messageType == TAKEN ->
            break; 
        fi;
    od;

}

init {
    chan init_mailbox = [10] of { mtype, MessageList };
    chan p1_mailbox = [10] of { mtype, MessageList };
    chan p2_mailbox = [10] of { mtype, MessageList };
    chan p3_mailbox = [10] of { mtype, MessageList };
    chan p4_mailbox = [10] of { mtype, MessageList };
    chan p5_mailbox = [10] of { mtype, MessageList };
    
    printf("Starting dining philosophers");
    int n = 5;
    int p1;
    
}