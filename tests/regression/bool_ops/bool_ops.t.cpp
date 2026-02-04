// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <bool_ops.h>

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
    // Test negation
    ASSERT(BoolOps::test_neg_t == false);
    ASSERT(BoolOps::test_neg_f == true);

    // Test and
    ASSERT(BoolOps::test_and_tt == true);
    ASSERT(BoolOps::test_and_tf == false);

    // Test or
    ASSERT(BoolOps::test_or_ff == false);
    ASSERT(BoolOps::test_or_ft == true);

    // Test xor
    ASSERT(BoolOps::test_xor_tt == false);
    ASSERT(BoolOps::test_xor_tf == true);

    // Test if
    ASSERT(BoolOps::test_if_t == 5u);
    ASSERT(BoolOps::test_if_f == 3u);

    // Test complex boolean expression
    ASSERT(BoolOps::test_complex == false); // (true && false) || (!true && true) = false || false

    // Test comparisons
    ASSERT(BoolOps::test_eq_tt == true);
    ASSERT(BoolOps::test_eq_tf == false);
    ASSERT(BoolOps::test_lt == true);

    return testStatus;
}
