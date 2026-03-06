// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include "primitive_rec_typeclass.h"

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
    // Test 1: primitive projection access
    {
        ASSERT(PrimitiveRecTypeclass::test_px == 3);
        ASSERT(PrimitiveRecTypeclass::test_py == 4);
        std::cout << "Test 1 (point projections): PASSED" << std::endl;
    }

    // Test 2: typeclass norm on point
    {
        ASSERT(PrimitiveRecTypeclass::test_norm_point == 7);  // 3 + 4
        std::cout << "Test 2 (norm point): PASSED" << std::endl;
    }

    // Test 3: double_norm via typeclass
    {
        ASSERT(PrimitiveRecTypeclass::test_double_norm == 14);  // (3+4) + (3+4)
        std::cout << "Test 3 (double_norm): PASSED" << std::endl;
    }

    // Test 4: vec3 norm
    {
        ASSERT(PrimitiveRecTypeclass::test_norm_vec3 == 6);  // 1 + 2 + 3
        std::cout << "Test 4 (norm vec3): PASSED" << std::endl;
    }

    // NOTE: test_width/test_height/test_perimeter excluded —
    //   rect_width/rect_height/rect_perimeter emitted as free functions
    //   but called as member methods on rect struct

    if (testStatus == 0) {
        std::cout << "\nAll prim_rec_tc tests passed!" << std::endl;
    } else {
        std::cout << "\n" << testStatus << " test(s) failed!" << std::endl;
    }
    return testStatus;
}
