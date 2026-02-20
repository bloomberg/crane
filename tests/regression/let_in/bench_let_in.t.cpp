// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <bench_let_in.h>

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
    // swap_snd(3, 4) = 4
    ASSERT(BenchLetIn::test_swap == 4u);

    // add_via_pair(3, 4) = 7
    ASSERT(BenchLetIn::test_add == 7u);

    // nested_swap(1, 2, 3, 4) = 1 + 4 = 5
    ASSERT(BenchLetIn::test_nested == 5u);

    // sum_via_pairs(5) = 5 + 4 + 3 + 2 + 1 = 15
    ASSERT(BenchLetIn::test_sum_pairs == 15u);

    // mid3(1, 2, 3) = 2
    ASSERT(BenchLetIn::test_mid3 == 2u);

    // sum3(1, 2, 3) = 6
    ASSERT(BenchLetIn::test_sum3 == 6u);

    // chain_pairs(1, 2, 3) = 1 + 3 = 4
    ASSERT(BenchLetIn::test_chain == 4u);

    return testStatus;
}
