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
    // === Implicit type arguments ===

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

    // === Implicit term arguments ===

    // Test add_implicit: 5 + 3 = 8
    ASSERT(ImplicitArgs::test_add_implicit == 8u);

    // Test scale: 3 * 7 = 21
    ASSERT(ImplicitArgs::test_scale == 21u);

    // Test combine: 2 + 3 + 4 = 9
    ASSERT(ImplicitArgs::test_combine == 9u);

    // Test apply_implicit: (add_one) 5 = 6
    ASSERT(ImplicitArgs::test_apply_implicit == 6u);

    // Test from_zero: 0 + 5 = 5
    ASSERT(ImplicitArgs::test_from_zero == 5u);

    // Test from_ten: 10 + 5 = 15
    ASSERT(ImplicitArgs::test_from_ten == 15u);

    // Test head_or empty: default = 0
    ASSERT(ImplicitArgs::test_head_empty == 0u);

    // Test head_or nonempty: head = 7
    ASSERT(ImplicitArgs::test_head_nonempty == 7u);

    // Test sum_with_init: 5 + 1 + 2 = 8
    ASSERT(ImplicitArgs::test_sum_init == 8u);

    // Test nested: 1 + 2 + 3 = 6
    ASSERT(ImplicitArgs::test_nested == 6u);

    // Test choose_branch true: 7
    ASSERT(ImplicitArgs::test_choose_true == 7u);

    // Test choose_branch false: 3
    ASSERT(ImplicitArgs::test_choose_false == 3u);

    return testStatus;
}
