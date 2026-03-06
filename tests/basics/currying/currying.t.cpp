// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <currying.h>

#include <functional>
#include <iostream>
#include <memory>
#include <string>
#include <variant>

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
    // Test add3: 1 + 2 + 3 = 6
    ASSERT(Currying::test_add3 == 6u);

    // Test partial1: 1 + 2 + 3 = 6
    ASSERT(Currying::test_partial1 == 6u);

    // Test partial2: 1 + 2 + 3 = 6
    ASSERT(Currying::test_partial2 == 6u);

    // Test curried: 3 + 4 = 7
    ASSERT(Currying::test_curried == 7u);

    // Test flip: 7 - 3 = 4 (flipped, so second arg - first arg)
    ASSERT(Currying::test_flip == 4u);

    // Test add_ten: 10 + 5 = 15
    ASSERT(Currying::test_add_ten == 15u);

    return testStatus;
}
