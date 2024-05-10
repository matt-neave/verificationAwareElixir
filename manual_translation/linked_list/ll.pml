

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

proctype __anonymous_0 (int x; chan ret; int __pid) {
ret ! x * x;
}

init {
    chan ret1 = [1] of { int };
    linked_list __test_ls;
    __list_append(__test_ls, 10);
    __list_append(__test_ls, 12);
    __list_append(__test_ls, 42);
    int x;
    x = __list_at(__test_ls, 1);
    linked_list __test_ls_new;
    __list_append(__test_ls_new, 420);
    __list_append_list(__test_ls_new, __test_ls);

    int a,b,c,d;
    a = __list_at(__test_ls_new, 0);
    b = __list_at(__test_ls_new, 1);
    c = __list_at(__test_ls_new, 2);
    d = __list_at(__test_ls_new, 3);
    printf("New list: [%d,%d,%d,%d]\n", a,b,c,d);


    // For loop implementation
    atomic {
        __list_ptr = 0;
        __list_ptr_new = 0;
        do
        :: __list_ptr >= LIST_LIMIT || __list_ptr_new >= LIST_LIMIT -> break;
        :: else ->
            if
            :: LIST_ALLOCATED(ls_old, __list_ptr) ->
            LIST_ALLOCATED(ls_new, __list_ptr_new) = true;
            LIST_VAL(ls_new, __list_ptr_new) = 
            // if assignment, write assignment variable here
            // loop body
            __list_ptr_new++;
            __list_ptr++;
            :: else -> __list_ptr++;
            fi
        od
    }
    }
}
