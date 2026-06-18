// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
//
// Test: missing any_cast when accessing projT2 of a SigT<Tag, any>.
// Bug 1: Crane calls .size() on std::any directly (should cast to deque<Val>)
// Bug 2: Crane calls .v() on std::any directly (should cast to Val)
//
// Reproduces parse-a-lot's JSON grammar action crash with DequeList mapping.
// The sigT stores sem_ty(nt) erased to any. When projT2 is used in a branch
// where the concrete type is known, Crane must emit any_cast<ConcreteType>.

#include "DequeElementCast.h"
#include <cassert>
#include <cstdio>

int main() {
    uint64_t r1 = DequeElementCast::DequeElementCast::test_count();
    assert(r1 == 3);

    uint64_t r2 = DequeElementCast::DequeElementCast::test_item_num();
    assert(r2 == 99);

    printf("test passed\n");
    return 0;
}
