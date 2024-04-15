int q;

init {
    int a[100];
    a[0] = 69
    // Prepend 42 to a
    int i;
    for (i : 0 .. 98) {
        int j;
        j = 99 - i;
        a[j] = a[j - 1];
    }
    a[0] = 42;
    q = a[0];
}

ltl { <>(q==69) }