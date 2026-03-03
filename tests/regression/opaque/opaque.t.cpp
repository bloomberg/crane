// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include "opaque.h"

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
    // Test 1: safe_pred (transparent proof via Defined)
    {
        ASSERT(Opaque::test_safe_pred == 4);
        std::cout << "Test 1 (safe_pred 5): PASSED" << std::endl;
    }

    // Test 2: pred_of_succ (uses opaque lemma as proof arg)
    {
        ASSERT(Opaque::test_pred_succ == 7);
        std::cout << "Test 2 (pred_of_succ 7): PASSED" << std::endl;
    }

    // Test 3: are_equal (transparent decision procedure via Defined)
    {
        ASSERT(Opaque::test_eq_true == true);
        ASSERT(Opaque::test_eq_false == false);
        std::cout << "Test 3 (are_equal): PASSED" << std::endl;
    }

    if (testStatus == 0) {
        std::cout << "\nAll opaque tests passed!" << std::endl;
    } else {
        std::cout << "\n" << testStatus << " test(s) failed!" << std::endl;
    }
    return testStatus;
}
