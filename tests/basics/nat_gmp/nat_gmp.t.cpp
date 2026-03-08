// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <nat_gmp.h>

#include <functional>
#include <iostream>
#include <memory>
#include <string>

// ============================================================================
//                     STANDARD ASSERT TEST FUNCTION
// ----------------------------------------------------------------------------

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
    // Basic arithmetic
    ASSERT(NatGMPTest::add_test(mpz_class(3), mpz_class(4)) == 7);
    ASSERT(NatGMPTest::mul_test(mpz_class(3), mpz_class(4)) == 12);
    ASSERT(NatGMPTest::sub_test(mpz_class(5), mpz_class(3)) == 2);
    ASSERT(NatGMPTest::sub_test(mpz_class(3), mpz_class(5)) == 0);

    // Comparisons
    ASSERT(NatGMPTest::eqb_test(mpz_class(3), mpz_class(3)) == true);
    ASSERT(NatGMPTest::eqb_test(mpz_class(3), mpz_class(4)) == false);
    ASSERT(NatGMPTest::ltb_test(mpz_class(3), mpz_class(4)) == true);
    ASSERT(NatGMPTest::ltb_test(mpz_class(4), mpz_class(3)) == false);
    ASSERT(NatGMPTest::leb_test(mpz_class(3), mpz_class(3)) == true);
    ASSERT(NatGMPTest::leb_test(mpz_class(4), mpz_class(3)) == false);

    // Pattern matching / pred
    ASSERT(NatGMPTest::pred_test(mpz_class(5)) == 4);
    ASSERT(NatGMPTest::pred_test(mpz_class(0)) == 0);
    ASSERT(NatGMPTest::match_test(mpz_class(0)) == 42);
    ASSERT(NatGMPTest::match_test(mpz_class(5)) == 4);

    // Numeral folding produces mpz_class(N) literals
    ASSERT(NatGMPTest::big_num == 200);
    ASSERT(NatGMPTest::another_big == 1000);
    ASSERT(NatGMPTest::add_big(mpz_class(10)) == 210);

    std::cout << "nat_gmp: all tests passed\n";

    return testStatus;
}
