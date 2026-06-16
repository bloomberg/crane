// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.

#include "erased_field_dangle.h"
#include <cassert>
#include <cstdio>

int main() {
    printf("test_unbox_nested = %llu\n", ErasedFieldDangle::test_unbox_nested);
    assert(ErasedFieldDangle::test_unbox_nested == 100);

    printf("test_unbox_compute = %llu\n", ErasedFieldDangle::test_unbox_compute);
    assert(ErasedFieldDangle::test_unbox_compute == 30);

    printf("test_chain_unbox = %llu\n", ErasedFieldDangle::test_chain_unbox);
    assert(ErasedFieldDangle::test_chain_unbox == 35);

    printf("test_hof_unbox = %llu\n", ErasedFieldDangle::test_hof_unbox);
    assert(ErasedFieldDangle::test_hof_unbox == 42);

    printf("test_exists = %llu\n", ErasedFieldDangle::test_exists);
    assert(ErasedFieldDangle::test_exists == 49);

    printf("All erased_field_dangle tests passed!\n");
    return 0;
}
