// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include "dep_elim.h"

#include <iostream>

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
    // Test 1: fin_to_nat
    {
        ASSERT(DepElim::test_fin0 == 0);
        ASSERT(DepElim::test_fin2 == 2);
        std::cout << "Test 1 (fin_to_nat): PASSED" << std::endl;
    }

    // Test 2: vec_to_list
    {
        auto l = DepElim::test_vec_list;
        unsigned int expected[] = {10, 20, 30};
        for (int i = 0; i < 3; i++) {
            auto &v = l->v();
            ASSERT(std::holds_alternative<List<unsigned int>::cons>(v));
            auto &c = std::get<List<unsigned int>::cons>(v);
            ASSERT(c._a0 == expected[i]);
            l = c._a1;
        }
        ASSERT(std::holds_alternative<List<unsigned int>::nil>(l->v()));
        std::cout << "Test 2 (vec_to_list): PASSED" << std::endl;
    }

    // Test 3: vec_head
    {
        ASSERT(DepElim::test_vec_head == 10);
        std::cout << "Test 3 (vec_head): PASSED" << std::endl;
    }

    // Test 4: get_present
    {
        ASSERT(DepElim::test_present == 42);
        std::cout << "Test 4 (get_present): PASSED" << std::endl;
    }

    if (testStatus == 0) {
        std::cout << "\nAll dep_elim tests passed!" << std::endl;
    } else {
        std::cout << "\n" << testStatus << " test(s) failed!" << std::endl;
    }
    return testStatus;
}
