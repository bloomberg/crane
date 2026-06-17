// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
//
// Test: spurious any_cast on concrete pair/deque fields in record destructuring.
// Same bug as sll_pair_cast but with DequeList mapping enabled.
// Crane generates any_cast<deque<any>>(l) on an already-concrete
// deque<sll_frame>. Causes bad_any_cast at runtime.

#include "SllPairCastDeque.h"
#include <cassert>
#include <cstdio>

int main() {
    bool r1 = SllPairCastDeque::SllPairCastDeque::test_final();
    assert(r1 == true);

    bool r2 = SllPairCastDeque::SllPairCastDeque::test_not_final();
    assert(r2 == false);

    printf("test passed\n");
    return 0;
}
