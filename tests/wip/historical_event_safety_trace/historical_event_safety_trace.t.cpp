#include "historical_event_safety_trace.h"

#include <cassert>

int main() {
    assert(HistoricalEventSafetyTraceCase::historical_lookup_1983(4u) == 200u);
    assert(HistoricalEventSafetyTraceCase::historical_lookup_1983(42u) == 0u);
    assert(HistoricalEventSafetyTraceCase::historical_lookup_2011(4u) == 400u);
    assert(HistoricalEventSafetyTraceCase::witness_test_initial_safe_at(10u));
    assert(HistoricalEventSafetyTraceCase::witness_test_peak_level_at(3u) > 0u);
    assert(HistoricalEventSafetyTraceCase::hoover_controller_sample(2050u) == 100u);
    assert(HistoricalEventSafetyTraceCase::hoover_controller_sample(1750u) == 25u);
    assert(HistoricalEventSafetyTraceCase::hoover_stage_sample(300u) == 60u);
    assert(HistoricalEventSafetyTraceCase::sample_bundle_test_count == 3u);
    assert(HistoricalEventSafetyTraceCase::sample_bundle_initial_safe);
    assert(HistoricalEventSafetyTraceCase::sample_bundle_hist_2011_id == 2011u);
    return 0;
}
