// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <nested_inductive.h>

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
    // Test root extraction
    ASSERT(NestedInductive::test_root_leaf == 5u);
    ASSERT(NestedInductive::test_root_small == 1u);

    // Test children count
    ASSERT(NestedInductive::test_children_leaf == 0u);
    ASSERT(NestedInductive::test_children_small == 2u);
    ASSERT(NestedInductive::test_children_bigger == 2u);

    return testStatus;
}
