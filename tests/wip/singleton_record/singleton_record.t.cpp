// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <singleton_record.h>

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
    // Test field access
    ASSERT(SingletonRecord::test_get == 5u);
    ASSERT(SingletonRecord::test_get2 == 5u);

    // Test pattern match unwrap
    ASSERT(SingletonRecord::test_unwrap == 5u);

    // Test double: 5 * 2 = 10
    ASSERT(SingletonRecord::test_double == 10u);

    // Test polymorphic unbox
    ASSERT(SingletonRecord::test_unbox == 3u);

    // Test double unbox
    ASSERT(SingletonRecord::test_double_unbox == 3u);

    // Test function wrapper: 1 + 7 = 8
    ASSERT(SingletonRecord::test_fn == 8u);

    return testStatus;
}
