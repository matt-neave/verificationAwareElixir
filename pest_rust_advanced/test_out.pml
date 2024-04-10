mtype = {VOTE};
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
chan mailbox[4] = [10] of { mtype, MessageList };

int maj;

init {
chan p0_mailbox = [10] of { mtype, MessageList };
chan ret1 = [1] of { int };
chan p1_mailbox = [10] of { mtype, MessageList };
chan ret2 = [1] of { int };
chan p2_mailbox = [10] of { mtype, MessageList };
chan ret3 = [1] of { int };
chan p3_mailbox = [10] of { mtype, MessageList };
chan ret4 = [1] of { int };
mailbox[1] = p1_mailbox;
mailbox[2] = p2_mailbox;
mailbox[3] = p3_mailbox;
mailbox[0] = p0_mailbox;
int __pid = 0;
run vote(__pid,ret1,1);
run vote(__pid,ret2,2);
run vote(__pid,ret3,3);
maj = run await_majority(3,0, ret4, __pid);
ret4 ? maj;
if
:: (maj > 1) -> 
printf("Majority reached\n");
:: else ->
printf("Majority not reached\n");
fi;
}

proctype await_majority (int n;int i; chan ret; int __pid) {
chan ret1 = [1] of { int };
if
:: (n == 0) -> 
ret ! i;
:: else ->
do
:: true ->
mtype messageType;
MessageList rec_v_0;
mailbox[__pid] ? messageType, rec_v_0;
if
:: messageType == VOTE ->
int x;
x = rec_v_0.m1.data2;
int val1;
run await_majority(n - 1,i + x, ret1, __pid);
ret1 ? val1;
ret ! val1;
break;
:: else -> mailbox[__pid] ! messageType, rec_v_0;
fi;
od;
fi;
}

proctype vote (int master; chan ret; int __pid) {
MessageList msg_0;
msg_0.m1.data2 = 1;
mailbox[master] ! VOTE, msg_0;
}


ltl ltl_0 { <>(maj>1) };