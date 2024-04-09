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
int x;
x = int x;
x = int x;
x = printf("x\n");
x
}

