#include <cstdio>
#include <cassert>
#include "DequeActionMismatch.h"

int main() {
    uint64_t len = DequeActionMismatch::test_length;
    printf("length: %llu\n", len);
    assert(len == 2);

    uint64_t fst = DequeActionMismatch::test_first;
    printf("first: %llu\n", fst);
    assert(fst == 42);

    printf("test passed\n");
    return 0;
}
