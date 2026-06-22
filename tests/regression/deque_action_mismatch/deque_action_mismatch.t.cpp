#include <cstdio>
#include <cassert>
#include "deque_action_mismatch.h"

int main() {
    uint64_t len = test_length;
    printf("length: %llu\n", len);
    assert(len == 2);

    uint64_t fst = test_first;
    printf("first: %llu\n", fst);
    assert(fst == 42);

    printf("test passed\n");
    return 0;
}
