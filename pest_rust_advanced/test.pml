
int value = 0;

init {
    value = 69;
    value = 420;
}

ltl ltl_0 { [](value==69 -> !<>(value==420) && value==420 -> !<>(value==69)) }