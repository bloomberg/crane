// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <eqordshow.h>

#include <iostream>
#include <string>

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
    // Test Eq class
    ASSERT(test_eq_true == true);
    ASSERT(test_eq_false == false);

    // Test neqb
    ASSERT(test_neq_true == true);
    ASSERT(test_neq_false == false);

    // Test Ord class (lt)
    ASSERT(test_lt_true == true);
    ASSERT(test_lt_false == false);

    // Test compare function
    ASSERT(std::holds_alternative<Ordering::ordering::LT>(test_compare_lt->v()));
    ASSERT(std::holds_alternative<Ordering::ordering::EQ>(test_compare_eq->v()));
    ASSERT(std::holds_alternative<Ordering::ordering::GT>(test_compare_gt->v()));

    // Test Show class
    ASSERT(test_show == "<nat>");

    if (testStatus == 0) {
        std::cout << "All tests passed!" << std::endl;
    }

    return testStatus;
}
