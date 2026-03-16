#include "epoch_cell_glyph_trace.h"

#include <cassert>

int main() {
    assert(EpochCellGlyphTraceCase::sample_total_lunar_count == 5u);
    assert(EpochCellGlyphTraceCase::sample_total_lunar_visible_count == 5u);
    assert(EpochCellGlyphTraceCase::sample_visible_series_checksum > 0u);

    assert(EpochCellGlyphTraceCase::sample_epoch_cell_zero);
    assert(EpochCellGlyphTraceCase::sample_epoch_glyph_match);
    assert(EpochCellGlyphTraceCase::sample_valid_epoch_visible);
    assert(EpochCellGlyphTraceCase::sample_valid_epoch_series_44);
    assert(EpochCellGlyphTraceCase::sample_valid_epoch_magnitude_ge_one);

    assert(EpochCellGlyphTraceCase::phase_code_after_steps(118u) == 2u);
    assert(EpochCellGlyphTraceCase::zodiac_code_after_steps(45u) == 1u);
    assert(EpochCellGlyphTraceCase::sample_step_roundtrip_saros);
    assert(EpochCellGlyphTraceCase::sample_olympiad_year_is_one_after_4);
    assert(EpochCellGlyphTraceCase::sample_eclipse_possible_after_6);
    assert(EpochCellGlyphTraceCase::sample_epoch_178_misaligned);

    return 0;
}
