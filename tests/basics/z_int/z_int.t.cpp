// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <z_int.h>

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
    ASSERT(ZIntTest::add_test(INT64_C(10), INT64_C(-3)) == 7);
    ASSERT(ZIntTest::mul_test(INT64_C(-4), INT64_C(5)) == -20);
    ASSERT(ZIntTest::sub_test(INT64_C(3), INT64_C(10)) == -7);
    ASSERT(ZIntTest::abs_test(INT64_C(-42)) == 42);
    ASSERT(ZIntTest::opp_test(INT64_C(5)) == -5);
    ASSERT(ZIntTest::opp_test(INT64_C(-3)) == 3);

    // Comparisons
    ASSERT(ZIntTest::eqb_test(INT64_C(3), INT64_C(3)) == true);
    ASSERT(ZIntTest::eqb_test(INT64_C(3), INT64_C(4)) == false);
    ASSERT(ZIntTest::ltb_test(INT64_C(-3), INT64_C(5)) == true);
    ASSERT(ZIntTest::ltb_test(INT64_C(5), INT64_C(-3)) == false);
    ASSERT(ZIntTest::leb_test(INT64_C(3), INT64_C(3)) == true);

    // Literals
    ASSERT(ZIntTest::zero_val == 0);
    ASSERT(ZIntTest::pos_val == 42);
    ASSERT(ZIntTest::neg_val == -7);
    ASSERT(ZIntTest::big_val == 1000);

    // Pattern matching
    ASSERT(ZIntTest::z_sign(INT64_C(5)) == 1);
    ASSERT(ZIntTest::z_sign(INT64_C(-3)) == -1);
    ASSERT(ZIntTest::z_sign(INT64_C(0)) == 0);

    std::cout << "z_int: all tests passed\n";
    return testStatus;
}
