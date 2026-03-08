// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <n_int.h>

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
    // Arithmetic
    ASSERT(NIntTest::add_test(3u, 4u) == 7u);
    ASSERT(NIntTest::mul_test(3u, 4u) == 12u);
    ASSERT(NIntTest::sub_test(5u, 3u) == 2u);
    ASSERT(NIntTest::sub_test(3u, 5u) == 0u);
    ASSERT(NIntTest::div_test(10u, 3u) == 3u);

    // Comparisons
    ASSERT(NIntTest::eqb_test(3u, 3u) == true);
    ASSERT(NIntTest::eqb_test(3u, 4u) == false);
    ASSERT(NIntTest::ltb_test(3u, 4u) == true);
    ASSERT(NIntTest::ltb_test(4u, 3u) == false);
    ASSERT(NIntTest::leb_test(3u, 3u) == true);

    // Unary
    ASSERT(NIntTest::succ_test(4u) == 5u);
    ASSERT(NIntTest::pred_test(5u) == 4u);
    ASSERT(NIntTest::pred_test(0u) == 0u);
    ASSERT(NIntTest::double_test(3u) == 6u);

    // Literals
    ASSERT(NIntTest::zero_val == 0u);
    ASSERT(NIntTest::five_val == 5u);
    ASSERT(NIntTest::big_val == 1000u);

    // Pattern matching
    ASSERT(NIntTest::is_zero(0u) == true);
    ASSERT(NIntTest::is_zero(5u) == false);

    // Positive
    ASSERT(NIntTest::pos_add(3u, 4u) == 7u);
    ASSERT(NIntTest::pos_succ(9u) == 10u);

    std::cout << "n_int: all tests passed\n";
    return testStatus;
}
