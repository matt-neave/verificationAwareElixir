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


proctype at (chan ret; int __pid) {
int ls[100];
ls[0] = 1;
ls[1] = 2;
ls[2] = 3;
int x;
x = ls[1];
printf("x\n");
}

init {
int ls[100];
ls[0] = 1;
ls[1] = 2;
ls[2] = 3;
int squares[100];
int __iterator;
for (__iterator : 0..2) {
int x;
x = ls[__iterator];
squares[__iterator] = x + x;
}
}


