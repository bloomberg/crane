#include <cstdio>
#include <cassert>
#include "DequeAnyCastElement.h"

int main() {
    uint64_t r = DequeAnyCastElement::test_result;
    assert(r == 3);
    printf("test passed\n");
    return 0;
}
