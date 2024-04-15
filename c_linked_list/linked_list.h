#include <stdio.h>
#include <stdlib.h>

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
}

LinkedList* append(LinkedList *head, int vals[], size_t size) {
    LinkedList *newNode = head;
    for (int i = 0; i < size; i++) {
        newNode->next = newLinkedList(vals[i]);
        newNode = newNode->next;
    }
    return head;
}


int example_main() {
    LinkedList *head = newLinkedList(69);
    head = prepend(head, 42);
    head = append(head, (int[]){1, 2, 3, 4, 5}, 5);
    printf("%d\n", head->val); // 42
    return 0;
};
