// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <sum.h>

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
    // Test is_left
    ASSERT(Sum::test_left == true);
    ASSERT(Sum::test_right == false);

    // Test either_to_nat
    ASSERT(Sum::test_either == 3u);

    // Test left_val is Left
    ASSERT((std::holds_alternative<Sum::either<unsigned int, bool>::Left>(Sum::left_val->v())));

    // Test right_val is Right
    ASSERT((std::holds_alternative<Sum::either<unsigned int, bool>::Right>(Sum::right_val->v())));

    // Test triple
    ASSERT((std::holds_alternative<Sum::triple<unsigned int, bool, unsigned int>::Second>(Sum::triple_test->v())));

    return testStatus;
}
