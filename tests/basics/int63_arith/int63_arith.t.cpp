// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include "int63_arith.h"

#include <iostream>

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
    // Test 1: constants
    {
        ASSERT(Int63Arith::i_zero == 0);
        ASSERT(Int63Arith::i_one == 1);
        std::cout << "Test 1 (constants): PASSED" << std::endl;
    }

    // Test 2: arithmetic
    {
        ASSERT(Int63Arith::i_add == 30);
        ASSERT(Int63Arith::i_mul == 42);
        ASSERT(Int63Arith::i_sub == 42);
        std::cout << "Test 2 (arithmetic): PASSED" << std::endl;
    }

    // Test 3: comparisons
    {
        ASSERT(Int63Arith::i_eqb_true == true);
        ASSERT(Int63Arith::i_eqb_false == false);
        ASSERT(Int63Arith::i_ltb_true == true);
        ASSERT(Int63Arith::i_ltb_false == false);
        ASSERT(Int63Arith::i_leb_true == true);
        ASSERT(Int63Arith::i_leb_false == false);
        std::cout << "Test 3 (comparisons): PASSED" << std::endl;
    }

    // Test 4: abs
    // Coq's int is unsigned 63-bit, so ltb x 0 is always false.
    // i_abs is effectively the identity function: i_abs x = x.
    // sub 0 42 wraps to 2^63 - 42, and i_abs returns it unchanged.
    {
        constexpr int64_t mask63 = 0x7FFFFFFFFFFFFFFFLL;
        ASSERT(Int63Arith::test_abs_pos == 42);
        ASSERT(Int63Arith::test_abs_neg == (mask63 - 42 + 1));
        std::cout << "Test 4 (abs): PASSED" << std::endl;
    }

    if (testStatus == 0) {
        std::cout << "\nAll int63_arith tests passed!" << std::endl;
    } else {
        std::cout << "\n" << testStatus << " test(s) failed!" << std::endl;
    }
    return testStatus;
}
