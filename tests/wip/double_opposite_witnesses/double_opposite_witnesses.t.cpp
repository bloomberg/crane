// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <cassert>

#include "double_opposite_witnesses.h"

int main()
{
    assert(DoubleOppositeWitnessesCase::forward_object_7 == 7u);
    assert(DoubleOppositeWitnessesCase::backward_object_9 == 9u);
    assert(DoubleOppositeWitnessesCase::forward_morphism_3 == 3u);
    assert(DoubleOppositeWitnessesCase::roundtrip_left_11 == 11u);
    assert(DoubleOppositeWitnessesCase::roundtrip_right_13 == 13u);
    assert(DoubleOppositeWitnessesCase::roundtrip_morphism_5 == 5u);
    assert(DoubleOppositeWitnessesCase::left_identity_code_11 == 1u);
    assert(DoubleOppositeWitnessesCase::right_identity_code_13 == 1u);
    assert(DoubleOppositeWitnessesCase::suspended_zero == 1u);
    return 0;
}
