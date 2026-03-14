#include "coalition_bid_honor_trace.h"

#include <cassert>

int main() {
    assert(CoalitionBidHonorTraceCase::sample_challenger_may_issue);
    assert(CoalitionBidHonorTraceCase::sample_coalition_bid_is_valid);
    assert(CoalitionBidHonorTraceCase::sample_coalition_contains_bear);
    assert(CoalitionBidHonorTraceCase::sample_updated_tonnage_reduced);

    assert(CoalitionBidHonorTraceCase::sample_attacker_ready_after_pass);
    assert(CoalitionBidHonorTraceCase::sample_attacker_not_ready_after_clear);
    assert(CoalitionBidHonorTraceCase::sample_phase_is_bidding);
    assert(CoalitionBidHonorTraceCase::sample_agreed_terminal);
    assert(CoalitionBidHonorTraceCase::sample_phase_depth_before_close == 1u);
    assert(CoalitionBidHonorTraceCase::sample_phase_depth_after_close == 0u);
    assert(CoalitionBidHonorTraceCase::sample_bidding_measure_reduced);

    assert(CoalitionBidHonorTraceCase::sample_challenge_honor_is_one);
    assert(CoalitionBidHonorTraceCase::sample_break_bid_honor_is_minus_ten);
    assert(CoalitionBidHonorTraceCase::sample_break_bid_actor_id == 1u);

    assert(CoalitionBidHonorTraceCase::sample_updated_bid_count < CoalitionBidHonorTraceCase::sample_attacker_bid_count);
    assert(CoalitionBidHonorTraceCase::sample_state_force_count > 0u);

    return 0;
}
