// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include "dep_record.h"

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
    // Test 1: monoid fold add
    {
        ASSERT(DepRecord::test_fold_add == 10);  // 1 + 2 + 3 + 4
        std::cout << "Test 1 (fold_add): PASSED" << std::endl;
    }

    // Test 2: monoid fold mul
    {
        ASSERT(DepRecord::test_fold_mul == 24);  // 2 * 3 * 4
        std::cout << "Test 2 (fold_mul): PASSED" << std::endl;
    }

    if (testStatus == 0) {
        std::cout << "\nAll dep_record tests passed!" << std::endl;
    } else {
        std::cout << "\n" << testStatus << " test(s) failed!" << std::endl;
    }
    return testStatus;
}
