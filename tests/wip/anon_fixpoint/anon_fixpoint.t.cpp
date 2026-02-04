// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <anon_fixpoint.h>

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
    // Test sum_to
    ASSERT(AnonFixpoint::test_sum_5 == 15u);
    ASSERT(AnonFixpoint::test_sum_0 == 0u);

    // Test factorial
    ASSERT(AnonFixpoint::test_fact_5 == 120u);
    ASSERT(AnonFixpoint::test_fact_0 == 1u);

    // Test double sum
    ASSERT(AnonFixpoint::test_double == 6u);

    // Test gcd
    ASSERT(AnonFixpoint::test_gcd == 6u);

    return testStatus;
}
