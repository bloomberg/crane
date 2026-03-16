// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <cassert>

#include "opposite_property_transfer_trace.h"

int main()
{
    assert(OppositePropertyTransferTraceCase::sample_opposite_tag == 7u);
    assert(OppositePropertyTransferTraceCase::sample_opposite_loop_value == 15u);
    assert(OppositePropertyTransferTraceCase::sample_result_seed == 6u);
    assert(OppositePropertyTransferTraceCase::sample_result_value == 22u);
    assert(OppositePropertyTransferTraceCase::sample_result_tag == 7u);
    assert(OppositePropertyTransferTraceCase::sample_checksum == 57u);
    return 0;
}
