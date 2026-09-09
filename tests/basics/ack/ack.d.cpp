// Differential test harness: prints canonical output for diffing against OCaml
#include <ack.h>
#include <cstdio>
int main() {
    printf("ack(0,0)=%u\n", Ack::ack(0, 0));
    printf("ack(0,1)=%u\n", Ack::ack(0, 1));
    printf("ack(0,5)=%u\n", Ack::ack(0, 5));
    printf("ack(1,0)=%u\n", Ack::ack(1, 0));
    printf("ack(1,1)=%u\n", Ack::ack(1, 1));
    printf("ack(1,5)=%u\n", Ack::ack(1, 5));
    printf("ack(2,0)=%u\n", Ack::ack(2, 0));
    printf("ack(2,1)=%u\n", Ack::ack(2, 1));
    printf("ack(2,2)=%u\n", Ack::ack(2, 2));
    printf("ack(2,4)=%u\n", Ack::ack(2, 4));
    printf("ack(3,0)=%u\n", Ack::ack(3, 0));
    printf("ack(3,1)=%u\n", Ack::ack(3, 1));
    printf("ack(3,2)=%u\n", Ack::ack(3, 2));
    printf("ack(3,3)=%u\n", Ack::ack(3, 3));
    printf("ack(3,7)=%u\n", Ack::ack(3, 7));
    return 0;
}
