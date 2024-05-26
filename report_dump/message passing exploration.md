```
mtype = { BIND }

chan c = [10] of { byte, mtype }

init {
    int a, b;
    a = run A();
    b = run B();
    c ! a, BIND;
    c ! b, BIND;
}
proctype A() {
    c ? 1, BIND;
    printf("%d bound\n", _pid);
}

proctype B() {
    c ? 2, BIND;
    printf("%d bound\n", _pid);
}

State-vector 60 byte, depth reached 10, errors: 0
       13 states, stored
        1 states, matched
       14 transitions (= stored+matched)
        0 atomic steps
hash conflicts:         0 (resolved)

Stats on memory usage (in Megabytes):
    0.001       equivalent memory usage for states (stored*(State-vector + overhead))
    0.292       actual memory usage for states
  128.000       memory used for hash table (-w24)
    0.534       memory used for DFS stack (-m10000)
  128.730       total actual memory usage


State-vector 204 byte, depth reached 10, errors: 0
       17 states, stored
        2 states, matched
       19 transitions (= stored+matched)
        0 atomic steps
hash conflicts:         0 (resolved)

Stats on memory usage (in Megabytes):
    0.004       equivalent memory usage for states (stored*(State-vector + overhead))
    0.292       actual memory usage for states
  128.000       memory used for hash table (-w24)
    0.534       memory used for DFS stack (-m10000)
  128.730       total actual memory usage
mtype = { BIND }

chan c[10] = [10] of { mtype };

  

init {

    int a, b;

    a = run A();

    b = run B();

  

    c[a] ! BIND;

    c[b] ! BIND;

}

  

proctype A() {

    c[_pid] ? BIND;

    printf("%d bound\n", _pid);

}

  

proctype B() {

    c[_pid] ? BIND;

    printf("%d bound\n", _pid);

}