// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include "coercions.h"

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
    // Test 1: bool coercion
    {
        ASSERT(Coercions::test_add_true == 6);
        ASSERT(Coercions::test_add_false == 5);
        std::cout << "Test 1 (bool coercion): PASSED" << std::endl;
    }

    // Test 2: record coercion
    {
        ASSERT(Coercions::test_double_wrapped == 14);
        std::cout << "Test 2 (record coercion): PASSED" << std::endl;
    }

    // Test 3: chained coercion
    {
        ASSERT(Coercions::test_add_boolbox == 11);
        std::cout << "Test 3 (chained coercion): PASSED" << std::endl;
    }

    // Test 4: function coercion
    {
        ASSERT(Coercions::test_fun_coercion == 10);
        std::cout << "Test 4 (function coercion): PASSED" << std::endl;
    }

    if (testStatus == 0) {
        std::cout << "\nAll coercions tests passed!" << std::endl;
    } else {
        std::cout << "\n" << testStatus << " test(s) failed!" << std::endl;
    }
    return testStatus;
}
