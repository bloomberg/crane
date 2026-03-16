#include "validated_pump_delivery_trace.h"

#include <cassert>

int main() {
    assert(ValidatedPumpDeliveryTraceCase::standard_result_code == 0u);
    assert(ValidatedPumpDeliveryTraceCase::standard_modified);
    assert(ValidatedPumpDeliveryTraceCase::standard_final_delivery_half == 50u);
    assert(ValidatedPumpDeliveryTraceCase::standard_pump_accepts);
    assert(ValidatedPumpDeliveryTraceCase::standard_reservoir_after == 1950u);
    assert(ValidatedPumpDeliveryTraceCase::mmol_result_code == 0u);
    assert(ValidatedPumpDeliveryTraceCase::mmol_final_delivery_tenth == 56u);
    assert(ValidatedPumpDeliveryTraceCase::high_iob_error_code == 9u);
    assert(ValidatedPumpDeliveryTraceCase::tdd_error_code == 8u);
    assert(ValidatedPumpDeliveryTraceCase::occlusion_error_code == 7u);
    assert(ValidatedPumpDeliveryTraceCase::battery_low_result_code == 0u);
    assert(ValidatedPumpDeliveryTraceCase::battery_low_pump_denied);
    assert(ValidatedPumpDeliveryTraceCase::pediatric_result_code == 0u);
    assert(ValidatedPumpDeliveryTraceCase::pediatric_modified);
    assert(ValidatedPumpDeliveryTraceCase::pediatric_final_delivery == 200u);
    assert(ValidatedPumpDeliveryTraceCase::low_reservoir_blocks);
    assert(ValidatedPumpDeliveryTraceCase::unknown_fault_blocks);
    return 0;
}
