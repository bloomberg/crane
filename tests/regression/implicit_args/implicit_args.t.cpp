// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <implicit_args.h>

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
    // Test identity
    ASSERT(ImplicitArgs::test_id == 5u);

    // Test fst_of
    ASSERT(ImplicitArgs::test_fst == 3u);

    // Test apply (double 5 = 10)
    ASSERT(ImplicitArgs::test_apply == 10u);

    // Test compose (double (add_one 3) = double 4 = 8)
    ASSERT(ImplicitArgs::test_compose == 8u);

    // Test length
    ASSERT(ImplicitArgs::test_length == 3u);

    // Test explicit id
    ASSERT(ImplicitArgs::test_explicit_id == 5u);

    // Test explicit fst
    ASSERT(ImplicitArgs::test_explicit_fst == 3u);

    return testStatus;
}
