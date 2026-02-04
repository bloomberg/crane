// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <let_in.h>

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
    // Test simple let
    ASSERT(LetIn::test_simple == 5u);

    // Test nested let
    ASSERT(LetIn::test_nested == 3u);

    // Test let with add
    ASSERT(LetIn::test_add == 7u);

    // Test shadowing
    ASSERT(LetIn::test_shadow == 3u);

    // Test let in function
    ASSERT(LetIn::test_fun_call == 6u);

    // Test let binding a function
    ASSERT(LetIn::test_let_fun == 6u);

    // Test destructuring
    ASSERT(LetIn::test_destruct == 3u);

    // Test multiple lets
    ASSERT(LetIn::test_multi == 6u);

    return testStatus;
}
