// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <prop_erasure.h>

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
    // Test that proof arguments are erased and values computed correctly
    ASSERT(PropErasure::test_use_proof == 5u);

    // Test simple value
    ASSERT(PropErasure::test_simple == 7u);

    // Test add with proof
    ASSERT(PropErasure::test_add_proof == 7u);

    return testStatus;
}
