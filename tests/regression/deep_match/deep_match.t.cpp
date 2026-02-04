// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <deep_match.h>

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
    // Test pair in list matching
    ASSERT(DeepMatch::test_pair_list == 5u);

    // Test matching on first two elements
    ASSERT(DeepMatch::test_two_one == 7u);
    ASSERT(DeepMatch::test_two_many == 7u);

    // Test triple nested
    ASSERT(DeepMatch::test_triple == 9u);

    // Test deep wildcard
    ASSERT(DeepMatch::test_wildcard == 1u);

    return testStatus;
}
