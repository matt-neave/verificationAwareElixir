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
mailbox[0] = p0_mailbox;
int __pid = 0;
int ls[100];
ls[0] = 1;
ls[1] = 2;
ls[2] = 3;
int __temp_iterable[3];
int __temp_iterator;
for (__temp_iterator : 0..2) {
__temp_iterable[__temp_iterator] = ls[__temp_iterator];
}
int x;
for (x in __temp_iterable) {
printf("x\n");
}
}


