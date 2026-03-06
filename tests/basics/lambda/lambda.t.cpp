// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <lambda.h>

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
    // Test simple lambda (identity)
    ASSERT(Lambda::test_simple == 5u);

    // Test multi-arg lambda: 3 + 4 = 7
    ASSERT(Lambda::test_multi == 7u);

    // Test nested: 1 + 2 + 3 = 6
    ASSERT(Lambda::test_nested == 6u);

    // Test adder: 3 + 5 = 8
    ASSERT(Lambda::test_adder == 8u);

    // Test let: 5 * 2 = 10
    ASSERT(Lambda::test_let == 10u);

    // Test apply: 5 + 1 = 6
    ASSERT(Lambda::test_apply == 6u);

    return testStatus;
}
