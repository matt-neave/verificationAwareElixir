mtype = {MESSAGE,FINISHED,BIND};
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
chan p0_mailbox = [10] of { mtype, MessageList };
chan ret1 = [1] of { int };
chan p1_mailbox = [10] of { mtype, MessageList };
chan ret2 = [1] of { int };
chan p2_mailbox = [10] of { mtype, MessageList };
chan ret3 = [1] of { int };
mailbox[1] = p1_mailbox;
mailbox[2] = p2_mailbox;
mailbox[0] = p0_mailbox;
int __pid = 0;
printf("BasicDeadlock running\n");
int p1;
p1 = run start_2(ret1,1);
int p2;
p2 = run start_2(ret2,2);
MessageList msg_0;
msg_0.m1.data2 = p2;
mailbox[1] ! BIND, msg_0;
MessageList msg_1;
msg_1.m1.data2 = p1;
mailbox[2] ! BIND, msg_1;
int val3;
run next_1(0, ret3, __pid);
ret3 ? val3;
}

proctype next_1 (int ps; chan ret; int __pid) {
chan ret1 = [1] of { int };
{
do /*15*/
:: true -> /*15*/
mtype messageType; /*15*/
MessageList rec_v_0; /*15*/
mailbox[__pid] ? messageType, rec_v_0; /*15*/
if /*15*/
:: messageType == FINISHED -> /*0*/
int val1;
run next_1(ps + 1, ret1, __pid);
ret1 ? val1;
ret ! val1;
break;
:: else -> mailbox[__pid] ! messageType, rec_v_0;
fi;
od;
}
unless
{(ps >= 2)
}
}

proctype start_2 (chan ret; int __pid) {
chan ret1 = [1] of { int };
printf("Process started\n");
do /*25*/
:: true -> /*25*/
mtype messageType; /*25*/
MessageList rec_v_1; /*25*/
mailbox[__pid] ? messageType, rec_v_1; /*25*/
if /*25*/
:: messageType == BIND -> /*26*/
int pid_other; /*26*/
pid_other = rec_v_1.m1.data2; /*26*/
printf("Bound\n");
int val1;
run next_2(pid_other, ret1, __pid);
ret1 ? val1;
ret ! val1;
break;
:: else -> mailbox[__pid] ! messageType, rec_v_1;
fi;
od;
}

proctype next_2 (int pid_other; chan ret; int __pid) {
chan ret1 = [1] of { int };
do /*34*/
:: true -> /*34*/
mtype messageType; /*34*/
MessageList rec_v_2; /*34*/
mailbox[__pid] ? messageType, rec_v_2; /*34*/
if /*34*/
:: messageType == MESSAGE -> /*35*/
MessageList msg_0;
mailbox[pid_other] ! MESSAGE, msg_0;
break;
:: else -> mailbox[__pid] ! messageType, rec_v_2;
fi;
od;
int val1;
run next_2(pid_other, ret1, __pid);
ret1 ? val1;
ret ! val1;
}


