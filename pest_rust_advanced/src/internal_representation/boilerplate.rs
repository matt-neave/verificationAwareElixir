// Helper functions for writing boilerplate code

pub fn add_linked_list_boiler_plate(mut model: String) -> String {
    model.push_str(
        "typedef __node {\n\
        int val;\n\
        bool allocated;\n\
    }\n\
    \n\
    #define MEM_LIMIT 40\n\
    #define LIST_LIMIT 10\n\
    \n\
    typedef __linked_list {\n\
        __node vals[LIST_LIMIT];\n\
        bool allocated;\n\
    }\n\
    \n\
    typedef __memory {\n\
        __linked_list lists[MEM_LIMIT];\n\
    }\n\
    \n\
    #define LIST(idx) __mem.lists[(idx)]\n\
    #define LIST_ALLOCATED(ls, idx) LIST(ls).vals[(idx)].allocated\n\
    #define LIST_VAL(ls, idx) LIST(ls).vals[(idx)].val\n\
    #define MEMORY_ALLOCATED(mem, idx) mem.lists[(idx)].allocated\n\
    #define __list_at(ls, idx) LIST(ls).vals[(idx)].val\n\
    \n\
    #define __MAILBOX(__pid) (__mailboxes[(__pid)])\n\
    \n\
    int __list_ptr;\n\
    int __list_last;\n\
    int __list_ptr_new;\n\
    int __list_ptr_old;\n\
    int __mem_ptr;\n\
    inline __list_append (ls, v)\n\
    {\n\
        atomic {\n\
            __list_ptr_old = __list_ptr;\n\
            __list_ptr = 0;\n\
            do\n\
            :: __list_ptr >= LIST_LIMIT -> 
                __list_ptr = __list_ptr_old;\n\
                break;\n\
            :: else ->\n\
                if\n\
                :: ! LIST_ALLOCATED(ls, __list_ptr) ->\n\
                LIST_ALLOCATED(ls, __list_ptr) = true;\n\
                LIST_VAL(ls, __list_ptr) = v;\n\
                break;\n\
                :: else -> __list_ptr++;\n\
                fi\n\
            od\n\
        }\n\
    }\n\
    \n\
    inline __list_pop (ls, v)\n\
    {\n\
        atomic {\n\
            __list_ptr_old = __list_ptr;\n\
            __list_ptr = LIST_LIMIT - 1;\n\
            do\n\
            :: __list_ptr < 0 ->
                __list_ptr = __list_ptr_old;\n\
                break;\n\
            :: else ->\n\
                if\n\
                :: LIST_ALLOCATED(ls, __list_ptr) ->\n\
                LIST_ALLOCATED(ls, __list_ptr) -> false;\n\
                LIST_VAL(ls, __list_ptr) = 0;\n\
                break;\n\
                :: else -> __list_ptr--;\n\
                fi\n\
        }\n\
    }\n\
    \n\
    inline __list_first (ls, assignee)\n\
    {\n\
        atomic {\n\
            __list_ptr_old = __list_ptr;\n\
            __list_ptr = 0;\n\
            do\n\
            :: __list_ptr >= LIST_LIMIT -> 
                __list_ptr = __list_ptr_old;\n\
                break;\n\
            :: else ->\n\
                if\n\
                :: LIST_ALLOCATED(ls, __list_ptr) ->\n\
                assignee = LIST_VAL(ls,__list_ptr);\n\
                break;\n\
                :: else -> __list_ptr++;\n\
                fi\n\
            od\n\
        }\n\
    }\n\
    \n\
    inline __list_update_at (ls, idx, v)\n\
    {\n\
        atomic {\n\
            if\n\
            :: LIST_ALLOCATED(ls,idx) ->\n\
            LIST_VAL(ls,idx) = v;\n\
            :: else ->\n\
            skip;\n\
            fi\n\
        }\n\
    }\n\
    \n\
    inline __list_remove_first (ls)\n\
    {\n\
        atomic {\n\
            __list_ptr_old = __list_ptr;\n\
            __list_ptr = 0;\n\
            do\n\
            :: __list_ptr >= LIST_LIMIT -> 
                __list_ptr = __list_ptr_old;\n\
                break;\n\
            :: else ->\n\
                if\n\
                :: LIST_ALLOCATED(ls, __list_ptr) ->\n\
                LIST_ALLOCATED(ls, __list_ptr) = false;\n\
                LIST_VAL(ls, __list_ptr) = 0;\n\
                break;\n\
                else -> __list_ptr++;\n\
                fi\n\
            od\n\
        }\n\
    }\n\
    \n\
    inline __list_random (ls, assignee)\n\
    {\n\
        atomic {\n\
            __list_ptr_old = __list_ptr;\n\
            __list_ptr = 0;\n\
            __list_last = 0;\n\
            do\n\
            :: __list_ptr < LIST_LIMIT ->\n\
                if \n\
                :: LIST_ALLOCATED(ls, __list_ptr) ->\n\
                    __list_last = __list_ptr;\n\
                :: else ->\n\
                    skip;\n\
                fi \n\
                __list_ptr++;\n\
            :: __list_ptr < LIST_LIMIT && LIST_ALLOCATED(ls, __list_ptr) ->\n\
                assignee = LIST_VAL(ls, __list_ptr);\n\
                __list_ptr = __list_ptr_old;\n\
                break;\n\
            :: __list_ptr >= LIST_LIMIT ->\n\
                assignee = LIST_VAL(ls, __list_last);\n\
                __list_ptr = __list_ptr_old;\n\
                break;\n\
            od\n\
        }\n\
    }\n\
    \n\
    inline __list_append_list (ls_new, ls_old)\n\
    {\n\
        atomic {\n\
            __list_ptr_old = __list_ptr;\n\
            __list_ptr = 0;\n\
            __list_ptr_new = 0;\n\
            do\n\
            :: __list_ptr >= LIST_LIMIT || __list_ptr_new >= LIST_LIMIT -> 
                __list_ptr = __list_ptr_old;\n\
                break;\n\
            :: else ->\n\
                if\n\
                :: ! LIST_ALLOCATED(ls_new, __list_ptr_new) ->\n\
                if \n\
                :: LIST_ALLOCATED(ls_old, __list_ptr) ->\n\
                    LIST_ALLOCATED(ls_new, __list_ptr_new) = true;\n\
                    LIST_VAL(ls_new, __list_ptr_new) = LIST_VAL(ls_old, __list_ptr);\n\
                    __list_ptr++;\n\
                    __list_ptr_new++;\n\
                :: else ->\n\
                    __list_ptr++;\n\
                fi\n\
                :: else ->\n\
                    __list_ptr_new++;\n\
                fi\n\
            od\n\
        }\n\
    }\n\
    \n\
    inline __get_next_memory_allocation (idx)\n\
    {\n\
        atomic {\n\
            __mem_ptr = 0;\n\
            do \n\
            :: __mem_ptr >= MEM_LIMIT -> break;\n\
            :: else ->\n\
                if\n\
                :: ! MEMORY_ALLOCATED(__mem, __mem_ptr) ->\n\
                MEMORY_ALLOCATED(__mem, __mem_ptr) = true;\n\
                idx = __mem_ptr;\n\
                break;\n\
                :: else -> __mem_ptr++;\n\
                fi\n\
            od\n\
        }\n\
    }\n\
    \n\
    inline __copy_memory_to_next (new_idx, old_idx)\n\
    {\n\
        atomic {\n\
            __list_ptr_old = __list_ptr;\n\
            __mem_ptr = 0;\n\
            do \n\
            :: __mem_ptr >= MEM_LIMIT -> break;\n\
            :: else ->\n\
                if\n\
                :: ! MEMORY_ALLOCATED(__mem, __mem_ptr) ->\n\
                MEMORY_ALLOCATED(__mem, __mem_ptr) = true;\n\
                __list_ptr = 0;\n\
                new_idx = __mem_ptr;\n\
                do\n\
                :: __list_ptr >= LIST_LIMIT -> break;\n\
                :: else ->\n\
                    LIST_ALLOCATED(__mem_ptr, __list_ptr) = LIST_ALLOCATED(old_idx, __list_ptr);\n\
                    LIST_VAL(__mem_ptr, __list_ptr) = LIST_VAL(old_idx, __list_ptr);\n\
                    __list_ptr++;\n\
                od\n\
                __list_ptr = __list_ptr_old;\n\
                break;\n\
                :: else -> __mem_ptr++;\n\
                fi\n\
            od\n\
        }\n\
    }\n\
    \n\
    int __dummy_iterator;\n\
    __memory __mem;\n\
    ");
    model
}