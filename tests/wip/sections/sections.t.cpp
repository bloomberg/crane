// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <sections.h>

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
    // Test section variable becomes parameter
    ASSERT(Sections::test_add == 7u);  // 5 + 2
    ASSERT(Sections::test_mul == 12u); // 3 * 4

    // Test nested sections
    ASSERT(Sections::test_nested == 8u); // 5 + 3

    // Test polymorphic identity
    ASSERT(Sections::test_id == 7u);

    // Test const
    ASSERT(Sections::test_const == 3u);

    return testStatus;
}
