// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
//
// Test: nested type scope resolution under separate extraction.
//
// The bug: Crane emits `Tag_` (unqualified) in template arguments for
// definitions outside the module, where it should emit `Tags::Tag_`.
// This causes a C++ compilation error: "unknown type name 'Tag_'".
//
// Expected: compilation failure due to unqualified Tag_ reference.

#include "NestedTypeScope.h"
#include <cassert>
#include <cstdio>

int main() {
    auto result = NestedTypeScope::test_tag;
    assert(result == NestedTypeScope::Tags::Tag_::BAR);
    printf("test passed\n");
    return 0;
}
