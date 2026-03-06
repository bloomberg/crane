// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include "sigma_types.h"

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
    // Test 1: use_nat_double 5 = 10
    {
        ASSERT(SigmaTypes::test_double_5 == 10);
        std::cout << "Test 1 (use_nat_double 5): PASSED" << std::endl;
    }

    // Test 2: get_positive 3 = 4
    {
        ASSERT(SigmaTypes::test_positive_3 == 4);
        std::cout << "Test 2 (get_positive 3): PASSED" << std::endl;
    }

    // Test 3: double_positive 3 = 8
    {
        ASSERT(SigmaTypes::test_double_pos == 8);
        std::cout << "Test 3 (double_positive 3): PASSED" << std::endl;
    }

    if (testStatus == 0) {
        std::cout << "\nAll sigma_compute tests passed!" << std::endl;
    } else {
        std::cout << "\n" << testStatus << " test(s) failed!" << std::endl;
    }
    return testStatus;
}
