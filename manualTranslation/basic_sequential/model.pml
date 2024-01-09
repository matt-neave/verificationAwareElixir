mtype = { NONE }
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
chan mailbox[1] = [10] of { mtype, MessageList };

// @Adds two numbers together but only works for positive inputs
proctype Add(int x; int y; chan ret) {
    if
    :: x < 0 || y < 0 ->
        ret ! (x * y);
    :: else ->
        ret ! (x + y);
    fi;
}

init {
    chan ret1 = [1] of { int };
    chan ret2 = [1] of { int };
    chan ret3 = [1] of { int };
    run Add(10, 12, ret1);
    int ret1_v;
    ret1 ? ret1_v;
    printf("%d", ret1_v);
    run Add(10, 12, ret2);
    int ret2_v;
    ret2 ? ret2_v;
    printf("%d", ret2_v);
    run Add(10, 12, ret3);
    int ret3_v;
    ret3 ? ret3_v;
    printf("%d", ret3_v);
}

