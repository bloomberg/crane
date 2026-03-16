#include "validated_virtual_crossmatch_trace.h"

#include <cassert>

int main() {
    assert(ValidatedVirtualCrossmatchTraceCase::sample_virtual_zero_negative);
    assert(ValidatedVirtualCrossmatchTraceCase::sample_dedup_count == 4u);
    assert(ValidatedVirtualCrossmatchTraceCase::sample_weak_acceptability);
    assert(ValidatedVirtualCrossmatchTraceCase::sample_strong_absolute_contra);
    assert(ValidatedVirtualCrossmatchTraceCase::sample_strong_has_complement_fixing_dsa);
    assert(ValidatedVirtualCrossmatchTraceCase::sample_strong_max_mfi == 9000u);
    assert(ValidatedVirtualCrossmatchTraceCase::sample_lab_id == 1u);
    assert(ValidatedVirtualCrossmatchTraceCase::sample_order_created);
    assert(ValidatedVirtualCrossmatchTraceCase::sample_order_blocked);
    assert(ValidatedVirtualCrossmatchTraceCase::sample_authorized_order_stays_authorized);
    return 0;
}
