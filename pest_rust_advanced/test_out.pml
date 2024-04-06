mtype = {OTHER,SUM,RES};
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
chan mailbox[2] = [10] of { mtype, MessageList };

init {
chan p0_mailbox = [10] of { mtype, MessageList };
chan ret1 = [1] of { int };
chan p1_mailbox = [10] of { mtype, MessageList };
mailbox[1] = p1_mailbox;
mailbox[0] = p0_mailbox;
int c_p;
c_p = run add(ret1);
MessageList msg_0;
msg_0.m1.data2 = 10;
msg_0.m2.data2 = 12;
msg_0.m3.data2 = _pid;
mailbox[1] ! SUM, msg_0;
do
:: true ->
mtype messageType;
MessageList rec_v_0;
mailbox[_pid] ? messageType, rec_v_0;
if
:: messageType == RES ->
int ans;
ans = rec_v_0.m1.data2
printf("ans\n");
break;
:: messageType == OTHER ->
printf("Unknown message\n");
break;
:: else -> mailbox[_pid] ! messageType, rec_v_0;
fi;
od;
}

proctype add (chan ret) {
do
:: true ->
mtype messageType;
MessageList rec_v_1;
mailbox[_pid] ? messageType, rec_v_1;
if
:: messageType == SUM ->
int x;
x = rec_v_1.m1.data2
int y;
y = rec_v_1.m2.data2
int from;
from = rec_v_1.m3.data2
MessageList msg_0;
msg_0.m1.data2 = x + y;
mailbox[from] ! RES, msg_0;
break;
:: messageType == OTHER ->
printf("Unknown message\n");
break;
:: else -> mailbox[_pid] ! messageType, rec_v_1;
fi;
od;
}

