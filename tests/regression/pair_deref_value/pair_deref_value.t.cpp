// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
//
// Test: spurious dereference of value-type field when destructuring
// std::pair (mapped from Coq prod) in functor-generated template code.
//
// The bug: When Mapping.Std maps `prod` to `std::pair`, Crane generates a
// conversion lambda that dereferences the second field as if it were a
// shared_ptr, but it's a value type (List<key>). This produces:
//   error: indirection requires pointer operand
//
// Expected: compilation failure.

#include "PairDerefValue.h"
#include <cassert>
#include <cstdio>

int main() {
    auto result = PairDerefValue::test_result;
    printf("test passed\n");
    return 0;
}
