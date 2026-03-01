// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include "higher_kinded.h"

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
    // Test 1: tree_sum
    {
        ASSERT(HigherKinded::test_tree_sum == 6);  // 1 + 2 + 3
        std::cout << "Test 1 (tree_sum): PASSED" << std::endl;
    }

    // Test 2: tree_size
    {
        ASSERT(HigherKinded::test_tree_size == 3);
        std::cout << "Test 2 (tree_size): PASSED" << std::endl;
    }

    if (testStatus == 0) {
        std::cout << "\nAll higher_kinded tests passed!" << std::endl;
    } else {
        std::cout << "\n" << testStatus << " test(s) failed!" << std::endl;
    }
    return testStatus;
}
