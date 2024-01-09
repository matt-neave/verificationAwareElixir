mtype = { NONE }

proctype Fibb(int n; chan ret) {
    chan ret1 = [1] of { int };
    chan ret2 = [1] of { int };
    if 
    :: n < 2 ->
        ret ! n
    :: else ->
        run Fibb(n - 1, ret1);
        int ret1_v;
        ret1 ? ret1_v;
        run Fibb(n - 2, ret2);
        int ret2_v;
        ret2 ? ret2_v;
        ret ! (ret1_v + ret2_v);
    fi;
}

init {
    chan ret1 = [1] of { int };
    run Fibb(10, ret1);
    int ret1_v;
    ret1 ? ret1_v;
    printf("Final was %d. \n", ret1_v);
}