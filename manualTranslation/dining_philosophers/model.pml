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
            printf("%d bound\n", _pid);
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
    msg_1.m1.data2 = self - 1;
    msg_1.m2.data2 = _pid
    mailbox[table] ! TAKE_CHOPSTICK, msg_1;

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
    msg_2.m1.data2 = (self) % n;
    msg_2.m2.data2 = _pid
    mailbox[table] ! TAKE_CHOPSTICK, msg_2;

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

    // TODO: model the remaining three sends
    printf("%d finished eating!\n", self);
}

init {
    chan init_mailbox = [10] of { mtype, MessageList };
    chan p1_mailbox = [10] of { mtype, MessageList };
    chan p2_mailbox = [10] of { mtype, MessageList };
    chan p3_mailbox = [10] of { mtype, MessageList };
    chan p4_mailbox = [10] of { mtype, MessageList };
    chan p5_mailbox = [10] of { mtype, MessageList };
    
    printf("Starting dining philosophers\n");
    int n = 5;
    // Unrolling of the for comprehension
    // TODO: can a for loop be used here?
    int p1;
    p1 = run Philosopher();
    mailbox[p1] = p1_mailbox;

    int p2;
    p2 = run Philosopher();
    mailbox[p2] = p2_mailbox;

    int p3;
    p3 = run Philosopher();
    mailbox[p3] = p3_mailbox;

    int p4;
    p4 = run Philosopher();
    mailbox[p4] = p4_mailbox;

    int p5;
    p5 = run Philosopher();
    mailbox[p5] = p5_mailbox;

    int i_1;
    for (i_1 : 1 .. n) {
        MessageList msg_1;
        msg_1.m1.data2 = _pid;
        msg_1.m2.data2 = i_1;
        msg_1.m3.data2 = n;
        mailbox[i_1] ! BIND, msg_1;
    }

    // Inline the recursive next function as a 
    // infinte loop that breaks when reaching 
    // the terminating state of the recursion
    int finished = 0;
    int chopsticks[5];
    do
    :: true ->
        if 
        :: finished == 5 ->
            printf("Break\n");
            break;
        :: finished < 5 ->
            do
            :: true ->
                MessageList rec_v_1;
                mtype messageType;
                mailbox[_pid] ? messageType, rec_v_1;
                printf("Message received\n");
                if
                :: messageType != TAKE_CHOPSTICK && 
                messageType != PLACE_CHOPSTICK &&
                messageType != FINISHED ->
                    mailbox[_pid] ! messageType, rec_v_1;
                :: messageType == TAKE_CHOPSTICK ->
                    printf("Received take chopstick from %d\n", rec_v_1.m2.data2);
                    if
                    :: chopsticks[rec_v_1.m1.data2] == 0 ->
                        mailbox[rec_v_1.m2.data2] ! TAKEN;
                        chopsticks[rec_v_1.m1.data2] = 1;
                        break;
                    :: else ->
                        break;
                    fi;
                :: messageType == PLACE_CHOPSTICK ->
                    chopsticks[rec_v_1.m1.data2] = 0;
                    break;
                :: messageType == FINISHED ->
                    finished = finished + 1;
                    break;
                fi;
            od;
        fi;
    od;
    printf("Finished");
}