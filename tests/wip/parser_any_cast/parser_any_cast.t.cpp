// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
//
// Test: incorrect type erasure with sigT — Crane generates code that uses
// std::any directly as a concrete type without any_cast.
//
// The bug: When a dependent type family (sem_ty : tag -> Type) is erased to
// std::any via sigT, Crane generates code like `return a1;` where a1 is
// std::any but the return type is uint64_t. It should emit
// `return std::any_cast<uint64_t>(a1);`.
//
// This is the root cause of the bad_any_cast crash in parse-a-lot's JSON
// parser, where semantic actions stored in sigT grammar entries are
// incorrectly cast at runtime.

#include "ParserAnyCast.h"
#include <cassert>
#include <cstdio>

int main() {
    uint64_t sum = ParserAnyCast::ParserAnyCast::test_sum();
    assert(sum == 42);
    printf("test passed: sum = %llu\n", (unsigned long long)sum);
    return 0;
}
