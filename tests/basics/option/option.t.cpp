// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <option.h>

#include <functional>
#include <iostream>
#include <memory>
#include <optional>
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
    // Test Some value
    ASSERT(Option::some_val.has_value());
    ASSERT(Option::some_val.value() == 5u);

    // Test None value
    ASSERT(!Option::none_val.has_value());

    // Test get_or_default
    ASSERT(Option::test_some == 5u);
    ASSERT(Option::test_none == 0u);

    // Test safe_pred
    ASSERT(!Option::test_pred_zero.has_value());
    ASSERT(Option::test_pred_five.has_value());
    ASSERT(Option::test_pred_five.value() == 4u);

    // Test nested options
    ASSERT(Option::nested_some.has_value());
    ASSERT(Option::nested_some.value().has_value());
    ASSERT(Option::nested_some.value().value() == 3u);

    ASSERT(Option::nested_none.has_value());
    ASSERT(!Option::nested_none.value().has_value());

    return testStatus;
}
