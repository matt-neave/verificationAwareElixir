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
MessageType m4;
MessageType m5;
MessageType m6;
};

chan __VOTE[10] = [10] of { mtype, MessageList };
chan __p0_VOTE = [10] of { mtype, MessageList };
chan __p1_VOTE = [10] of { mtype, MessageList };
chan __p2_VOTE = [10] of { mtype, MessageList };
chan __p3_VOTE = [10] of { mtype, MessageList };
typedef node {
int val;
bool allocated;
}

typedef linked_list {
node vals[10];
}

#define LIST_LIMIT 10

#define LIST_ALLOCATED(ls, idx) ls.vals[(idx)].allocated
#define LIST_VAL(ls, idx) ls.vals[(idx)].val
#define __list_at(ls, idx) ls.vals[(idx)].val

int __list_ptr;
int __list_last;
int __list_ptr_new;
inline __list_append (ls, v)
{
atomic {
__list_ptr = 0;
do
:: __list_ptr >= LIST_LIMIT -> break;
:: else ->
if
:: ! LIST_ALLOCATED(ls, __list_ptr) ->
LIST_ALLOCATED(ls, __list_ptr) = true;
LIST_VAL(ls, __list_ptr) = v;
break;
:: else -> __list_ptr++;
fi
od
}
}

inline __list_pop (ls, v)
{
atomic {
__list_ptr = LIST_LIMIT - 1;
do
:: __list_ptr < 0 -> break;
:: else ->
if
:: LIST_ALLOCATED(ls, __list_ptr) ->
LIST_ALLOCATED(ls, __list_ptr) -> false;
LIST_VAL(ls, __list_ptr) = 0;
break;
:: else -> __list_ptr--;
fi
}
}

inline __list_first (ls, assignee)
{
atomic {
__list_ptr = 0;
do
:: __list_ptr >= LIST_LIMIT -> break;
:: else ->
if
:: LIST_ALLOCATED(ls, __list_ptr) ->
assignee = LIST_VAL(ls,__list_ptr);
break;
:: else -> __list_ptr++;
fi
od
}
}

inline __list_update_at (ls, idx, v)
{
atomic {
if
:: LIST_ALLOCATED(ls,idx) ->
LIST_VAL(ls,idx) = v;
:: else ->
skip;
fi
}
}

inline __list_remove_first (ls)
{
atomic {
__list_ptr = 0;
do
:: __list_ptr >= LIST_LIMIT -> break;
:: else ->
if
:: LIST_ALLOCATED(ls, __list_ptr) ->
LIST_ALLOCATED(ls, __list_ptr) = false;
LIST_VAL(ls, __list_ptr) = 0;
break;
else -> __list_ptr++;
fi
od
}
}

inline __list_random (ls, assignee)
{
atomic {
__list_ptr = 0;
__list_last = 0;
do
:: __list_ptr < LIST_LIMIT ->
if 
:: LIST_ALLOCATED(ls, __list_ptr) ->
__list_last = __list_ptr;
:: else ->
skip;
fi 
__list_ptr++;
:: __list_ptr < LIST_LIMIT && LIST_ALLOCATED(ls, __list_ptr) ->
assignee = LIST_VAL(ls, __list_ptr);
break;
:: __list_ptr >= LIST_LIMIT ->
assignee = LIST_VAL(ls, __list_last);
break;
od
}
}

inline __list_append_list (ls_new, ls_old)
{
atomic {
__list_ptr = 0;
__list_ptr_new = 0;
do
:: __list_ptr >= LIST_LIMIT || __list_ptr_new >= LIST_LIMIT -> break;
:: else ->
if
:: ! LIST_ALLOCATED(ls_new, __list_ptr_new) ->
if 
:: LIST_ALLOCATED(ls_old, __list_ptr) ->
LIST_ALLOCATED(ls_new, __list_ptr_new) = true;
LIST_VAL(ls_new, __list_ptr_new) = LIST_VAL(ls_old, __list_ptr);
__list_ptr++;
__list_ptr_new++;
:: else ->
__list_ptr++;
fi
:: else ->
__list_ptr_new++;
fi
od
}
}
int maj;

init {
chan ret1 = [1] of { int }; /*6*/
__VOTE[0] = __p0_VOTE;
__VOTE[1] = __p1_VOTE;
__VOTE[2] = __p2_VOTE;
__VOTE[3] = __p3_VOTE;
int __pid = 0;
if
::__pid==-1 -> __pid = _pid;
::else->skip;
fi;
run run_consensus(ret1, __pid); /*6*/
}

proctype run_consensus (chan ret; int __pid) {
chan ret1 = [1] of { int };
chan ret2 = [1] of { int };
chan ret3 = [1] of { int };
chan ret4 = [1] of { int }; /*15*/
chan ret5 = [1] of { int }; /*19*/
if
::__pid==-1 -> __pid = _pid;
::else->skip;
fi;
run vote(__pid,ret1,-1); /*12*/
run vote(__pid,ret2,-1); /*13*/
run vote(__pid,ret3,-1); /*14*/
maj = run await_majority(3,0, ret4, __pid); /*15*/
ret4 ? maj; /*15*/
;
if
:: (maj > 1) -> /*0*/
printf("Majority reached\n");
:: else ->
run run_consensus(ret5, __pid); /*19*/
fi;
}

proctype await_majority (int n;int i; chan ret; int __pid) {
chan ret1 = [1] of { int }; /*29*/
if
::__pid==-1 -> __pid = _pid;
::else->skip;
fi;
if
:: (n == 0) -> /*0*/
ret ! i; /*26*/
:: else ->
MessageList rec_v_0; /*28*/
do /*28*/
:: __VOTE[__pid] ? VOTE, rec_v_0 -> /*29*/
int x; /*29*/
x = rec_v_0.m1.data2; /*29*/
run await_majority(n - 1,i + x, ret1, __pid); /*29*/
int __ret_placeholder_1; /*29*/
ret1 ? __ret_placeholder_1; /*29*/
ret ! __ret_placeholder_1; /*29*/
break;
od;
fi;
}

proctype vote (int master; chan ret; int __pid) {
if
::__pid==-1 -> __pid = _pid;
::else->skip;
fi;
linked_list options;
__list_append(options, 0);
__list_append(options, 1);
int choice;
choice = __list_random(options, choice);
;
MessageList msg_0; /*40*/
msg_0.m1.data2 = choice; /*40*/
__VOTE[master] ! VOTE, msg_0; /*40*/
}


ltl ltl_0 { <>(maj>1) };