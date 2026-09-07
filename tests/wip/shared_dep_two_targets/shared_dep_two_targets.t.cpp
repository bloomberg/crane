// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <shared_dep_two_targets.h>
#include <shared_dep_two_targets_b.h>
#include <cassert>
#include <cstdint>

int main()
{
    assert(SharedDepTwoTargets::test);
    assert(!SharedDepTwoTargetsB::test2);
    return 0;
}
