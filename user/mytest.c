#include "../kernel/types.h"
#include "../user/user.h"
#include "../kernel/fcntl.h"
#include "../kernel/syscall.h"
//#include "../kernel/defs.h"

void handler1()
{
    printf("Consider yourself handled 1!");
}
void handler2()
{
    printf("Consider yourself handled 2!");
}
void testSigaction()
{
    int signum = 1;
    struct sigaction *sigact;
    struct sigaction *oldact;
    sigact = malloc(sizeof(struct sigaction));
    oldact = malloc(sizeof(struct sigaction));
    sigact->sigmask = 1 << 5;
    sigact->sa_handler = &handler2;
    printf("Sending mask: %d\nSending hanler address: %d\n", sigact->sigmask, sigact->sa_handler);
    sigaction(signum, sigact, oldact);
}
void testSigRet()
{
    sigret();
}
void testKill()
{
    kill(1,2);
}
int main(int argc, char *argv[])
{
    testKill();
    exit(0);
}