

typedef node {
    int val;
    bool allocated;
}

typedef linked_list {
    chan val = [10] of {int};
    chan allocated = [10] of {bool};
}

#define LIST_LIMIT 10

#define LIST_ALLOCATED(ls, idx) ls.allocated[(idx)]
#define LIST_VAL(ls, idx) ls.val[(idx)]

int __list_ptr;
int __list_last;
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

init {
    __list_append(__init_ls, 10);
    __list_append(__init_ls, 12);
    __list_append(__init_ls, 42);
    __list_remove_first(__init_ls);
    int x;
    __list_random(__init_ls, x);
    printf("Val: %d\n", x);
}

