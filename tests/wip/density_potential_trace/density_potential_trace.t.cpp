// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <cassert>

#include "density_potential_trace.h"

int main()
{
    assert(DensityPotentialTraceCase::static_time_nonnegative_at(1u));
    assert(DensityPotentialTraceCase::density_radicand_nonnegative_at(1u));
    assert(DensityPotentialTraceCase::density_value_nonnegative_at(1u));
    assert(DensityPotentialTraceCase::massive_potential_nonnegative_at(2u));
    assert(DensityPotentialTraceCase::sample_static_nonneg);
    assert(DensityPotentialTraceCase::sample_density_radicand_nonneg);
    assert(DensityPotentialTraceCase::sample_density_value_nonneg);
    assert(DensityPotentialTraceCase::sample_massive_nonneg);
    return 0;
}
