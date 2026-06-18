// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
//
// Test: demonstrate DequeList + type erasure incompatibility.
//
// The bug: cons calls wrap elements in std::any() because the carrier
// type is erased, but mfold<nat_monoid> is monomorphized and expects
// deque<uint64_t>. The type mismatch causes a compile error.
// A related issue: Crane previously generated std::deque<auto>{} for
// nil (now fixed to std::deque<std::any>{}).
//
// Expected: compile error (deque<std::any> vs deque<uint64_t> mismatch)

#include "deque_any_cast.h"
#include <cassert>
#include <cstdio>

int main() {
    auto result = DequeAnyCast::test_fold_add;
    assert(result == 6);
    printf("test passed: fold = %llu\n", (unsigned long long)result);
    return 0;
}
