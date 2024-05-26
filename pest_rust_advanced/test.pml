mtype = { BIND }
chan c = [10] of { byte, mtype }


init {
    int a, b;
    a = run A();
    b = run B();

    c ! b, BIND;
    c ! a, BIND;
}

proctype A() {
    c ? eval(_pid), BIND;
    printf("%d bound\n", _pid);
}

proctype B() {
    c ? eval(_pid), BIND;
    printf("%d bound\n", _pid);
}