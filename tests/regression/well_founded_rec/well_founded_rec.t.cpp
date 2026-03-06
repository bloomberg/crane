// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include "well_founded_rec.h"

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
    // Test 1: div2
    {
        ASSERT(WellFoundedRec::test_div2_0 == 0);
        ASSERT(WellFoundedRec::test_div2_1 == 0);
        ASSERT(WellFoundedRec::test_div2_7 == 3);
        ASSERT(WellFoundedRec::test_div2_10 == 5);
        std::cout << "Test 1 (div2_wf): PASSED" << std::endl;
    }

    // Test 2: gcd
    {
        ASSERT(WellFoundedRec::test_gcd_1 == 4);   // gcd(12,8) = 4
        ASSERT(WellFoundedRec::test_gcd_2 == 7);   // gcd(35,14) = 7
        ASSERT(WellFoundedRec::test_gcd_3 == 5);   // gcd(0,5) = 5
        std::cout << "Test 2 (gcd_wf): PASSED" << std::endl;
    }

    if (testStatus == 0) {
        std::cout << "\nAll acc_rect tests passed!" << std::endl;
    } else {
        std::cout << "\n" << testStatus << " test(s) failed!" << std::endl;
    }
    return testStatus;
}
