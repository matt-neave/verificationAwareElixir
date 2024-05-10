init {
  atomic {
    printf("Hi");
    atomic {
      printf("World");
    }
  }
}