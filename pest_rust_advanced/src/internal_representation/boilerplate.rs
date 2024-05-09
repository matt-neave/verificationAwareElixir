// Helper functions for writing boilerplate code

pub fn add_linked_list_boiler_plate(mut model: String) -> String {
    model.push_str(
        "typedef node {\n\
        int val;\n\
        bool allocated;\n\
    }\n\
    \n\
    typedef linked_list {\n\
        node vals[10];\n\
    }\n\
    \n\
    #define LIST_LIMIT 10\n\
    \n\
    #define LIST_ALLOCATED(ls, idx) ls.vals[(idx)].allocated\n\
    #define LIST_VAL(ls, idx) ls.vals[(idx)].val\n\
    \n\
    int __list_ptr;\n\
    int __list_last;\n\
    inline __list_append (ls, v)\n\
    {\n\
        atomic {\n\
            __list_ptr = 0;\n\
            do\n\
            :: __list_ptr >= LIST_LIMIT -> break;\n\
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
            __list_ptr = LIST_LIMIT - 1;\n\
            do\n\
            :: __list_ptr < 0 -> break;\n\
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
            __list_ptr = 0;\n\
            do\n\
            :: __list_ptr >= LIST_LIMIT -> break;\n\
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
            __list_ptr = 0;\n\
            do\n\
            :: __list_ptr >= LIST_LIMIT -> break;\n\
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
                break;\n\
            :: __list_ptr >= LIST_LIMIT ->\n\
                assignee = LIST_VAL(ls, __list_last);\n\
                break;\n\
            od\n\
        }\n\
    }\n\
    ");
    model
}