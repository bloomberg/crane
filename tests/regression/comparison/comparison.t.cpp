// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <comparison.h>

#include <functional>
#include <iostream>
#include <memory>
#include <string>
#include <variant>

namespace {

int testStatus = 0;

void aSsErT(bool condition, const char *message, int line)
{
    if (condition) {
        std::cout << "Error " __FILE__ "(" << line << "): " << message
             << "    (failed)" << std::endl;

        if (0 <= testStatus && testStatus <= 100) {
            ++testStatus;
        }
    }
}

}  // close unnamed namespace

#define ASSERT(X)                                              \
    aSsErT(!(X), #X, __LINE__);

int main() {
    // Test cmp_to_nat
    ASSERT(Comparison::test_lt_nat == 0u);
    ASSERT(Comparison::test_eq_nat == 1u);
    ASSERT(Comparison::test_gt_nat == 2u);

    // Test compare_nats returns correct cmp value
    ASSERT(Comparison::test_compare_lt == Comparison::cmp::CmpLt);
    ASSERT(Comparison::test_compare_eq == Comparison::cmp::CmpEq);
    ASSERT(Comparison::test_compare_gt == Comparison::cmp::CmpGt);

    // Test max/min
    ASSERT(Comparison::test_max == 7u);
    ASSERT(Comparison::test_min == 3u);

    // Test clamp
    ASSERT(Comparison::test_clamp_lo == 3u);   // 1 clamped to 3
    ASSERT(Comparison::test_clamp_mid == 5u);  // 5 unchanged
    ASSERT(Comparison::test_clamp_hi == 7u);   // 9 clamped to 7

    // Test flip
    ASSERT(Comparison::test_flip == Comparison::cmp::CmpGt);

    return testStatus;
}
