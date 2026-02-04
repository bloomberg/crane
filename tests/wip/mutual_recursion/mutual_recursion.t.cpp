// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <mutual_recursion.h>

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
    // Test even/odd
    ASSERT(MutualRecursion::test_even_0 == true);
    ASSERT(MutualRecursion::test_even_4 == true);
    ASSERT(MutualRecursion::test_odd_3 == true);
    ASSERT(MutualRecursion::test_odd_4 == false);

    // Test tree size
    ASSERT(MutualRecursion::test_size_simple == 2u);  // 2 leaves
    ASSERT(MutualRecursion::test_size_nested == 2u);  // 2 leaves (3 and 4)

    // Test tree sum
    ASSERT(MutualRecursion::test_sum_simple == 3u);   // 1 + 2
    ASSERT(MutualRecursion::test_sum_nested == 7u);   // 3 + 4

    return testStatus;
}
