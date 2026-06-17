// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
//
// Test: spurious any_cast on concrete pair fields in record destructuring.
// Crane generates any_cast<pair<any,any>> on an already-concrete
// pair<sll_frame, list<sll_frame>> when the record is matched with
// a nested pattern. Causes bad_any_cast at runtime.
//
// Reproduces parse-a-lot's SLLPrediction::sll_final_config crash.

#include "SllPairCast.h"
#include <cassert>
#include <cstdio>

int main() {
    bool r1 = SllPairCast::SllPairCast::test_final();
    assert(r1 == true);

    bool r2 = SllPairCast::SllPairCast::test_not_final();
    assert(r2 == false);

    printf("test passed\n");
    return 0;
}
