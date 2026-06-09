// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
//
// Test: demonstrate DequeList + type erasure incompatibility.
//
// The bug manifests in multiple ways:
// 1. Compile error: Crane generates std::deque<auto>{} for nil when the
//    element type is erased (auto is not valid in template arguments).
// 2. Runtime bad_any_cast (in more complex cases like parse-a-lot PPM):
//    Crane generates any_cast<Datatypes::List<T>> but the runtime value
//    is actually std::deque<T> due to the DequeList mapping.
//
// Expected: compile error on std::deque<auto>

#include "deque_any_cast.h"
#include <cassert>
#include <cstdio>

int main() {
    auto result = DequeAnyCast::test_fold_add;
    assert(result == 6);
    printf("test passed: fold = %llu\n", (unsigned long long)result);
    return 0;
}
