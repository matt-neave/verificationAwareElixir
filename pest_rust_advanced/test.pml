init {
chan ret1 = [1] of { int };
chan ret2 = [1] of { int };
chan ret3 = [1] of { int };
run add(1024,12, ret1);
int val1;
ret1 ? val1
run add(0,12, ret2);
int val2;
ret2 ? val2
run add(-2,12, ret3);
int val3;
ret3 ? val3
}

proctype add (int x;int y; chan ret) {
if
:: (true || true) -> 
ret ! x * y
else ->
ret ! x + y
fi
}

