// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include "nested_ind_stdlib_list.h"

#include <iostream>
#include <vector>

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

// Helper: convert List<unsigned int> to std::vector
std::vector<unsigned int>
to_vector(const std::shared_ptr<List<unsigned int>> &l) {
    std::vector<unsigned int> result;
    auto cur = l;
    while (true) {
        auto ok = std::visit(
            Overloaded{
                [&](const List<unsigned int>::nil) -> bool {
                    return false;
                },
                [&](const List<unsigned int>::cons args) -> bool {
                    result.push_back(args._a0);
                    cur = args._a1;
                    return true;
                }},
            cur->v());
        if (!ok) break;
    }
    return result;
}


int main() {
    // Test 1: eval(1 + 2 + 3) = 6
    {
        ASSERT(NestedIndStdlibList::test_eval_add == 6);
        std::cout << "Test 1 (eval add): PASSED" << std::endl;
    }

    // Test 2: eval(2 * 3 * 4) = 24
    {
        ASSERT(NestedIndStdlibList::test_eval_mul == 24);
        std::cout << "Test 2 (eval mul): PASSED" << std::endl;
    }

    // Test 3: eval((1+2) * (3+4)) = 21
    {
        ASSERT(NestedIndStdlibList::test_eval_nested == 21);
        std::cout << "Test 3 (eval nested): PASSED" << std::endl;
    }

    // Test 4: literals of (1+2)*(3+4) = [1,2,3,4]
    {
        auto v = to_vector(NestedIndStdlibList::test_literals);
        ASSERT(v.size() == 4);
        ASSERT(v[0] == 1);
        ASSERT(v[1] == 2);
        ASSERT(v[2] == 3);
        ASSERT(v[3] == 4);
        std::cout << "Test 4 (literals): PASSED" << std::endl;
    }

    if (testStatus == 0) {
        std::cout << "\nAll nested_ind tests passed!" << std::endl;
    } else {
        std::cout << "\n" << testStatus << " test(s) failed!" << std::endl;
    }
    return testStatus;
}
