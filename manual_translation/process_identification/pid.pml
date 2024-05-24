mtype = { BIND }
chan mailbox[10] = [3] of { mtype }

int mailboxes[100];
int __next_mailbox = 0;
#define __MAILBOX(__pid) (mailboxes[__pid])
inline __new_mailbox(idx) {
    d_step {
        mailboxes[idx] = __next_mailbox;
        __next_mailbox++;
    }
}

init {
    __new_mailbox(_pid);
    run A(2);
    run A(2);
    int a;
    d_step {
        a = run A(-1);
        __new_mailbox(a);
    }
    mailbox[__MAILBOX(a)] ! BIND;
    mailbox[__MAILBOX(_pid)] ! BIND;
    mailbox[__MAILBOX(_pid)] ! BIND;
}

proctype A(int __pid) {
if
::__pid==-1 -> __pid = _pid;
::else->skip;
fi;
mailbox[__MAILBOX(__pid)] ? BIND;
}