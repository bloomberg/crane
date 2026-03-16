// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <cassert>

#include "polygon_winding_area_trace.h"

int main()
{
    assert(PolygonWindingAreaTraceCase::inside_by_winding(
               PolygonWindingAreaTraceCase::test_centroid,
               PolygonWindingAreaTraceCase::test_triangle));
    assert(!PolygonWindingAreaTraceCase::inside_by_winding(
                PolygonWindingAreaTraceCase::test_exterior,
                PolygonWindingAreaTraceCase::test_triangle));
    assert(PolygonWindingAreaTraceCase::nonnegative_area(
               PolygonWindingAreaTraceCase::test_triangle));
    assert(PolygonWindingAreaTraceCase::nonnegative_area(
               PolygonWindingAreaTraceCase::test_equatorial_square(
                   PolygonWindingAreaTraceCase::sample_square_delta)));
    assert(PolygonWindingAreaTraceCase::sample_centroid_inside);
    assert(!PolygonWindingAreaTraceCase::sample_exterior_inside);
    assert(PolygonWindingAreaTraceCase::sample_triangle_area_nonnegative);
    assert(PolygonWindingAreaTraceCase::sample_square_area_nonnegative);
    assert(PolygonWindingAreaTraceCase::sample_first_angle_nonnegative);
    assert(PolygonWindingAreaTraceCase::sample_centroid_winding_gt_half);
    return 0;
}
