// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
//
// Test: incorrect type erasure with sigT — two bugs:
// 1. Crane uses crane::obj field directly as concrete type without any_cast
// 2. Crane emits any_cast<crane::obj>(monostate{}) when the erased type family
//    returns unit for a specific branch. This crashes at runtime because
//    monostate is stored inside the any, not crane::obj.
//
// Bug #2 reproduces parse-a-lot's defLiteral crash:
//   static const sem_ty v = crane::any_cast<sem_ty>(std::monostate{});
// where sem_ty = crane::obj. Should just be: crane::obj(std::monostate{}).

#include "ParserAnyCast.h"
#include <cassert>
#include <cstdio>

int main() {
    uint64_t sum = ParserAnyCast::ParserAnyCast::test_sum();
    assert(sum == 42);

    auto label = ParserAnyCast::ParserAnyCast::test_default_label();
    assert(label == ParserAnyCast::ParserAnyCast::Label::UNITL);

    printf("test passed\n");
    return 0;
}
