// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.

#include "erased_multi_index.h"
#include <cassert>
#include <cinttypes>
#include <cstdio>

int main() {
    printf("test_tagged = %" PRIu64 "\n", ErasedMultiIndex::test_tagged);
    assert(ErasedMultiIndex::test_tagged == 42);

    printf("test_hlist = %" PRIu64 "\n", ErasedMultiIndex::test_hlist);
    assert(ErasedMultiIndex::test_hlist == 3);

    printf("All erased_multi_index tests passed!\n");
    return 0;
}
