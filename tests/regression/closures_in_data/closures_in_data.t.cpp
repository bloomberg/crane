// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include "closures_in_data.h"

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
    // Test 1: compose_all pipeline 3 = ((3+1)*2)+10 = 18
    {
        ASSERT(ClosuresInData::test_compose == 18);
        std::cout << "Test 1 (compose pipeline): PASSED" << std::endl;
    }

    // Test 2: maybe_apply None 42 = 42
    {
        ASSERT(ClosuresInData::test_maybe_none == 42);
        std::cout << "Test 2 (maybe_apply None): PASSED" << std::endl;
    }

    // Test 3: maybe_apply (Some S) 41 = 42
    {
        ASSERT(ClosuresInData::test_maybe_some == 42);
        std::cout << "Test 3 (maybe_apply Some): PASSED" << std::endl;
    }

    if (testStatus == 0) {
        std::cout << "\nAll closures_in_data tests passed!" << std::endl;
    } else {
        std::cout << "\n" << testStatus << " test(s) failed!" << std::endl;
    }
    return testStatus;
}
