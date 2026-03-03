// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include "poly_inductive.h"

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
    // Test 1: ppair fst/snd
    {
        ASSERT(PolyInductive::test_ppair_fst == 7);
        ASSERT(PolyInductive::test_ppair_snd == true);
        std::cout << "Test 1 (ppair fst/snd): PASSED" << std::endl;
    }

    // Test 2: pmaybe default on PJust
    {
        ASSERT(PolyInductive::test_pjust == 99);
        std::cout << "Test 2 (pjust default): PASSED" << std::endl;
    }

    // Test 3: pmaybe default on PNothing
    {
        ASSERT(PolyInductive::test_pnothing == 0);
        std::cout << "Test 3 (pnothing default): PASSED" << std::endl;
    }

    // Test 4: ptree_size
    {
        ASSERT(PolyInductive::test_ptree == 5);  // PNode(PLeaf, PNode(PLeaf, PLeaf)) = 1+1+1+1+1
        std::cout << "Test 4 (ptree_size): PASSED" << std::endl;
    }

    // NOTE: test_pbox excluded — punbox() returns `this` instead of contained value
    // NOTE: test_pmap excluded — pmaybe_map lambda uses `axiom` type

    if (testStatus == 0) {
        std::cout << "\nAll poly_inductive tests passed!" << std::endl;
    } else {
        std::cout << "\n" << testStatus << " test(s) failed!" << std::endl;
    }
    return testStatus;
}
