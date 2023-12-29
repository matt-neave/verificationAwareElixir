# Steps involved in manual translation of Elixir to Promela

- Determine all the message types and create `mtype`
- Determine the number of processes, need to count calls to spawn. There can be multiple ways spawn is called i.e. in a for comprehension, using Node.spawn or just spawning processes.
- Create a mailbox channel for each process.
- The size of the channels could be set by a command line argument, but default to 10.
- Identify and create the `init` process (this may need to be marked via metaprogramming or other methods i.e. comments)
- We will require a `start` function in the `init` module. This is to identify what code should run to initialise the model. This could also be annotated instead of explicit.
- The `start` function can be directly included in the `init` body.
- Promela is strongly typed unlike Elixir, so we can use basic type inference during variable initialisation to determine the type.
- Processes can be created sequentially, and named pn. For comprehensions can be unrolled.
- The start of any body of model that is to create processes should also create the relevenat mailboxes `pn_mailbox`. The init process should also have a mailbox, indexed at 0 in the mailbox.

Here is the structure of a mailbox. We need to allow for messages of any type to be stored, this makes handling a receive simple as we can extract the parameter, mn from the `MessageType`. We can use static analysis on the program to determine the longest message and use that to define how many message parameters we need.

```
typedef MessageType {
    mtype type;
    byte data1[20];
    int data2;
    byte data3[20];
    bool data4;
};
typedef MessageList {
    MessageType m1;
    MessageType m2;
    MessageType m3;
    MessageType m4;
    MessageType m5;
};
chan mailbox[6] = [10] of { mtype, MessageList };
```

### Modelling Processes
Modelling processes is more difficult. Some considerations need to be made.

- Recursive function calls are difficult to model.
- Non-recursive function calls can be inlined into their body where necessairy! We can store the code translation for a function call in the rust function lookup directory, and in-line every call to it!
- Generally avoid heavy functional code and recursive calls at first, we can factor them in later. The main priority should be sequential programs such as the `basic_deadlock` and `basic_livelock` examples.
- In translation, `self()` is `_pid`.
- Modulo exists in Promela, and should be mapped to from `rem`.

Example of creating a message:
```
MessageList msg_2;
msg_2.m1.data2 = (self + 1) % n;
msg_2.m2.data2 = _pid
mailbox[_pid] ! TAKE_CHOPSTICK, msg_2;
```