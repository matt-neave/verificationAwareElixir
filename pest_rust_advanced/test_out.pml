mtype = {BIND,FINISHED,MESSAGE};
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
chan mailbox[3] = [10] of { mtype, MessageList };

init {
chan ret1 = [1] of { int };
chan p1_mailbox = [10] of { mtype, MessageList };
chan ret2 = [1] of { int };
chan p2_mailbox = [10] of { mtype, MessageList };
chan ret3 = [1] of { int };
mailbox[1] = p1_mailbox;
mailbox[2] = p2_mailbox;
printf("BasicDeadlock running\n");
int p1;
p1 = run start_2(ret1);
int p2;
p2 = run start_2(ret2);
MessageList msg_0;
msg_0.m1.data2 = p2;
mailbox[1] ! BIND, msg_0;
MessageList msg_1;
msg_1.m1.data2 = p1;
mailbox[2] ! BIND, msg_1;
run next_1(0, ret3);
int val3;
ret3 ? val3
}

proctype next_1 (int ps; chan ret) {
chan ret1 = [1] of { int };
{
do
:: true ->
mtype messageType;
MessageList rec_v_0;
mailbox[_pid] ? messageType, rec_v_0;
if
:: messageType == FINISHED ->
run next_1(ps + 1, ret1);
int val1;
ret1 ? val1
break;
:: else -> mailbox[_pid] ! messageType, rec_v_0;
fi;
od;
}
unless
{(ps >= 2)
}
}

proctype start_2 (chan ret) {
chan ret1 = [1] of { int };
printf("Process started\n");
do
:: true ->
mtype messageType;
MessageList rec_v_1;
mailbox[_pid] ? messageType, rec_v_1;
if
:: messageType == BIND ->
int pid_other;
pid_other = rec_v_1.m1.data2
printf("Bound\n");
run next_2(pid_other, ret1);
int val1;
ret1 ? val1
break;
:: else -> mailbox[_pid] ! messageType, rec_v_1;
fi;
od;
}

proctype next_2 (int pid_other; chan ret) {
chan ret1 = [1] of { int };
do
:: true ->
mtype messageType;
MessageList rec_v_2;
mailbox[_pid] ? messageType, rec_v_2;
if
:: messageType == MESSAGE ->
MessageList msg_0;
mailbox[pid_other] ! MESSAGE, msg_0;
break;
:: else -> mailbox[_pid] ! messageType, rec_v_2;
fi;
od;
run next_2(pid_other, ret1);
int val1;
ret1 ? val1
}

