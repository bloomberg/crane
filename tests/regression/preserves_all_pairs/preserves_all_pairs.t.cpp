// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <preserves_all_pairs.h>
#include <cassert>
#include <iostream>

int main()
{
    assert(PreservesAllPairs::t == true);
    std::cout << "Test passed." << std::endl;
    return 0;
}
