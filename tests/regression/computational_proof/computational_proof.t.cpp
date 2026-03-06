// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include "computational_proof.h"

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

#define ASSERT(X) aSsErT(!(X), #X, __LINE__);


int main() {
    // Test 1: nat_eq_dec
    {
        ASSERT(ComputationalProof::test_eq_true == true);
        ASSERT(ComputationalProof::test_eq_false == false);
        std::cout << "Test 1 (nat_eqb_dec): PASSED" << std::endl;
    }

    // Test 2: nat_leb_dec
    {
        ASSERT(ComputationalProof::test_leb_true == true);
        ASSERT(ComputationalProof::test_leb_false == false);
        std::cout << "Test 2 (nat_leb_dec): PASSED" << std::endl;
    }

    // Test 3: min/max
    {
        ASSERT(ComputationalProof::test_min == 4);
        ASSERT(ComputationalProof::test_max == 9);
        std::cout << "Test 3 (min/max_dec): PASSED" << std::endl;
    }

    if (testStatus == 0) {
        std::cout << "\nAll comp_proof tests passed!" << std::endl;
    } else {
        std::cout << "\n" << testStatus << " test(s) failed!" << std::endl;
    }
    return testStatus;
}
