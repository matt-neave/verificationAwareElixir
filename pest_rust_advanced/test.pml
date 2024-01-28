init {
chan ret1 = [1] of { int };
chan ret2 = [1] of { int };
chan ret3 = [1] of { int };
run add(ret1, 1024, 12);
int val;
ret1 ? val
run add(ret2, 0, 12);
int val2;
ret2 ? val2
run add(ret3, -2, 12);
int val3;
ret3 ? val3
}

proctype add (chan ret; int x; int y) {
if
:: (true || true) -> 
ret ! (x * y);
else ->
ret ! (x + y);
fi
}

