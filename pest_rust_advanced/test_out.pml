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

c_decl {
typedef struct LinkedList {
int val;
struct LinkedList *next;
} LinkedList;

LinkedList* newLinkedList(int val) {
LinkedList *newNode = (LinkedList *)malloc(sizeof(LinkedList));
newNode->val = val;
newNode->next = NULL;
return newNode;
};

LinkedList* prepend(LinkedList *head, int val) {
LinkedList *newNode = (LinkedList *)malloc(sizeof(LinkedList));
newNode->val = val;
newNode->next = head;
return newNode;
};

LinkedList* append(LinkedList *head, int vals[], size_t size) {
LinkedList *newNode = head;
for (int i = 0; i < size; i++) {
newNode->next = newLinkedList(vals[i]);
newNode = newNode->next;
};
return head;
};
}


init{ 
int x[100];
x[0] = 1;
x[1] = 2;
int y[100];
y[0] = 1;
y[1] = x[0];
y[2] = x[1];
int head;
head = y[0];
printf("head\n");
}


