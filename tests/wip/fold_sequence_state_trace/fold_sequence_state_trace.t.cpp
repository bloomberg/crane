// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <cassert>

#include "fold_sequence_state_trace.h"

int main()
{
    const auto recomputed_line_count =
        FoldSequenceStateTraceCase::line_count_after_sample_sequence(
            FoldSequenceStateTraceCase::initial_state);

    assert(FoldSequenceStateTraceCase::sample_sequence_length == 3u);
    assert(FoldSequenceStateTraceCase::sample_point_count == 2u);
    assert(recomputed_line_count == 5u);
    assert(FoldSequenceStateTraceCase::sample_lines_nonempty);
    assert(FoldSequenceStateTraceCase::sample_has_expected_lines);
    return 0;
}
