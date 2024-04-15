int q;

// c_decl { 
//     typedef struct LinkedList {
//         int val;
//         struct LinkedList *next;
//     } LinkedList;

//     LinkedList* newLinkedList(int val) {
//         LinkedList *newNode = (LinkedList *)malloc(sizeof(LinkedList));
//         newNode->val = val;
//         newNode->next = NULL;
//         return newNode;
//     };

//     LinkedList* prepend(LinkedList *head, int val) {
//         LinkedList *newNode = (LinkedList *)malloc(sizeof(LinkedList));
//         newNode->val = val;
//         newNode->next = head;
//         return newNode;
//     }

//     LinkedList* append(LinkedList *head, int vals[], size_t size) {
//         LinkedList *newNode = head;
//         for (int i = 0; i < size; i++) {
//             newNode->next = newLinkedList(vals[i]);
//             newNode = newNode->next;
//         }
//         return head;
//     }
// }

c_decl {
    \#include "linked_list.h" 
}

c_state "LinkedList *head" "Global"

init {
    c_code {
        now.head = newLinkedList(69);
    }
    c_code {
        now.head = prepend(now.head, 42);
    }
    c_code {
        now.head = append(now.head, (int[]){1,2,3}, 3);
    }
    c_code {
        now.q = now.head->val;
    }
}

ltl { <>(q==42) }
