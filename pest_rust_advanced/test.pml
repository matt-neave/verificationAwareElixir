
init {
    int a = 1;

    do
    :: a <= 10000 -> a = a + 1;
    :: a > 10000 -> break;
    od;
    printf("Hello World\n");
}

ltl ltl_0 { (false)&&(<>([]true)) }