// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <n_gmp.h>

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
    ASSERT(NGMPTest::add_test(mpz_class(3), mpz_class(4)) == 7);
    ASSERT(NGMPTest::mul_test(mpz_class(3), mpz_class(4)) == 12);
    ASSERT(NGMPTest::sub_test(mpz_class(5), mpz_class(3)) == 2);
    ASSERT(NGMPTest::sub_test(mpz_class(3), mpz_class(5)) == 0);
    ASSERT(NGMPTest::div_test(mpz_class(10), mpz_class(3)) == 3);

    // Comparisons
    ASSERT(NGMPTest::eqb_test(mpz_class(3), mpz_class(3)) == true);
    ASSERT(NGMPTest::eqb_test(mpz_class(3), mpz_class(4)) == false);
    ASSERT(NGMPTest::ltb_test(mpz_class(3), mpz_class(4)) == true);
    ASSERT(NGMPTest::ltb_test(mpz_class(4), mpz_class(3)) == false);
    ASSERT(NGMPTest::leb_test(mpz_class(3), mpz_class(3)) == true);

    // Unary
    ASSERT(NGMPTest::succ_test(mpz_class(4)) == 5);
    ASSERT(NGMPTest::pred_test(mpz_class(5)) == 4);
    ASSERT(NGMPTest::pred_test(mpz_class(0)) == 0);
    ASSERT(NGMPTest::double_test(mpz_class(3)) == 6);

    // Literals
    ASSERT(NGMPTest::zero_val == 0);
    ASSERT(NGMPTest::five_val == 5);
    ASSERT(NGMPTest::big_val == 1000);

    // Pattern matching
    ASSERT(NGMPTest::is_zero(mpz_class(0)) == true);
    ASSERT(NGMPTest::is_zero(mpz_class(5)) == false);

    // Positive
    ASSERT(NGMPTest::pos_add(mpz_class(3), mpz_class(4)) == 7);
    ASSERT(NGMPTest::pos_succ(mpz_class(9)) == 10);

    std::cout << "n_gmp: all tests passed\n";
    return testStatus;
}
