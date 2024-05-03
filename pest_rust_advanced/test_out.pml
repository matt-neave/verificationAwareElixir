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
chan mailbox[1] = [10] of { mtype, MessageList };


init {
chan p0_mailbox = [10] of { mtype, MessageList };
chan ret1 = [1] of { int };
chan ret2 = [1] of { int };
chan ret3 = [1] of { int };
mailbox[0] = p0_mailbox;
int __pid = 0;
int val1;
run add(1024,12, ret1, __pid);
ret1 ? val1;
int val2;
run add(0,12, ret2, __pid);
ret2 ? val2;
int val3;
run add(-2,12, ret3, __pid);
ret3 ? val3;
}

proctype add (int x;int y; chan ret; int __pid) {
if
:: (true || false) -> 
ret ! x * y;
:: else ->
fi;
}


