// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include "typeclasses.h"

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
    // Test 1: to_nat on nat (identity)
    {
        ASSERT(Typeclasses::test_nat == 42);
        std::cout << "Test 1 (to_nat nat): PASSED" << std::endl;
    }

    // Test 2: to_nat on bool
    {
        ASSERT(Typeclasses::test_bool_true == 1);
        ASSERT(Typeclasses::test_bool_false == 0);
        std::cout << "Test 2 (to_nat bool): PASSED" << std::endl;
    }

    // Test 3: numeric_double
    {
        ASSERT(Typeclasses::test_double == 14);
        std::cout << "Test 3 (numeric_double 7): PASSED" << std::endl;
    }

    // Test 4: sort_pair via Ord superclass
    {
        ASSERT(Typeclasses::test_sort_pair.first == 3);
        ASSERT(Typeclasses::test_sort_pair.second == 5);
        std::cout << "Test 4 (sort_pair 5 3): PASSED" << std::endl;
    }

    // Test 5: min_of / max_of via Ord
    {
        ASSERT(Typeclasses::test_min == 3);
        ASSERT(Typeclasses::test_max == 8);
        std::cout << "Test 5 (min/max): PASSED" << std::endl;
    }

    // Test 6: describe with multi-constraint (Numeric + Eq)
    {
        ASSERT(Typeclasses::test_describe_eq == 5);   // eqb 5 5 = true, so to_nat 5
        ASSERT(Typeclasses::test_describe_ne == 10);  // eqb 3 7 = false, so 3 + 7
        std::cout << "Test 6 (describe): PASSED" << std::endl;
    }

    if (testStatus == 0) {
        std::cout << "\nAll typeclasses tests passed!" << std::endl;
    } else {
        std::cout << "\n" << testStatus << " test(s) failed!" << std::endl;
    }
    return testStatus;
}
