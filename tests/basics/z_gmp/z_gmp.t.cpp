// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <z_gmp.h>

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
    ASSERT(ZGMPTest::add_test(mpz_class(10), mpz_class(-3)) == 7);
    ASSERT(ZGMPTest::mul_test(mpz_class(-4), mpz_class(5)) == -20);
    ASSERT(ZGMPTest::sub_test(mpz_class(3), mpz_class(10)) == -7);
    ASSERT(ZGMPTest::abs_test(mpz_class(-42)) == 42);
    ASSERT(ZGMPTest::opp_test(mpz_class(5)) == -5);
    ASSERT(ZGMPTest::opp_test(mpz_class(-3)) == 3);

    // Comparisons
    ASSERT(ZGMPTest::eqb_test(mpz_class(3), mpz_class(3)) == true);
    ASSERT(ZGMPTest::eqb_test(mpz_class(3), mpz_class(4)) == false);
    ASSERT(ZGMPTest::ltb_test(mpz_class(-3), mpz_class(5)) == true);
    ASSERT(ZGMPTest::ltb_test(mpz_class(5), mpz_class(-3)) == false);
    ASSERT(ZGMPTest::leb_test(mpz_class(3), mpz_class(3)) == true);

    // Literals
    ASSERT(ZGMPTest::zero_val == 0);
    ASSERT(ZGMPTest::pos_val == 42);
    ASSERT(ZGMPTest::neg_val == -7);
    ASSERT(ZGMPTest::big_val == 1000);

    // Pattern matching
    ASSERT(ZGMPTest::z_sign(mpz_class(5)) == 1);
    ASSERT(ZGMPTest::z_sign(mpz_class(-3)) == -1);
    ASSERT(ZGMPTest::z_sign(mpz_class(0)) == 0);

    std::cout << "z_gmp: all tests passed\n";
    return testStatus;
}
