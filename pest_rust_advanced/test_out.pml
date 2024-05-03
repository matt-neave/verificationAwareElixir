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
mailbox[0] = p0_mailbox;
int __pid = 0;
int val1;
run clock(0, ret1, __pid);
ret1 ? val1;
}

proctype clock (int n; chan ret; int __pid) {
if
:: (n == 12) -> 
printf("Done\n");
:: else ->
fi;
}


ltl ltl_0 { []((n>=1)&&(n<=12)) };