#include "record_field_patterns.h"

uint64_t
RecordFieldPatterns::classify_point(const RecordFieldPatterns::Point &p) {
  uint64_t x = p.px;
  uint64_t y = p.py;
  if (x <= 0) {
    if (y <= 0) {
      return UINT64_C(0);
    } else {
      uint64_t _x = y - 1;
      return UINT64_C(1);
    }
  } else {
    uint64_t _x = x - 1;
    if (y <= 0) {
      return UINT64_C(2);
    } else {
      uint64_t _x0 = y - 1;
      return (x + y);
    }
  }
}

uint64_t RecordFieldPatterns::zero_x(const RecordFieldPatterns::Point &p) {
  uint64_t px0 = p.px;
  uint64_t n = p.py;
  if (px0 <= 0) {
    return n;
  } else {
    uint64_t m = px0 - 1;
    return (m + n);
  }
}

/// Apply a polymorphic function to a record — the record type flows
/// through a type variable.
RecordFieldPatterns::Point
RecordFieldPatterns::id_point(const RecordFieldPatterns::Point &_x0) {
  return identity<RecordFieldPatterns::Point>(_x0);
}

std::pair<uint64_t, uint64_t>
RecordFieldPatterns::point_pair(const RecordFieldPatterns::Point &p) {
  return std::make_pair(p.px, p.py);
}

uint64_t RecordFieldPatterns::first_coord(const RecordFieldPatterns::Point &p) {
  return generic_first<uint64_t, uint64_t>(point_pair(p));
}

uint64_t
RecordFieldPatterns::scaled_sum(uint64_t scale,
                                const RecordFieldPatterns::ScaledPoint &sp) {
  uint64_t x = sp.sp_x;
  uint64_t y = sp.sp_y;
  return (scale * (x + y));
}

RecordFieldPatterns::Point RecordFieldPatterns::PointImpl::mk(uint64_t x,
                                                              uint64_t x0) {
  return Point{x, x0};
}

uint64_t
RecordFieldPatterns::PointImpl::get_x(const RecordFieldPatterns::Point &p) {
  return p.px;
}

uint64_t
RecordFieldPatterns::PointImpl::get_y(const RecordFieldPatterns::Point &p) {
  return p.py;
}

uint64_t
RecordFieldPatterns::segment_length_sq(const RecordFieldPatterns::Segment &s) {
  RecordFieldPatterns::Point seg_start0 = s.seg_start;
  RecordFieldPatterns::Point seg_end0 = s.seg_end;
  uint64_t x1 = seg_start0.px;
  uint64_t y1 = seg_start0.py;
  uint64_t x2 = seg_end0.px;
  uint64_t y2 = seg_end0.py;
  uint64_t dx = (((x2 - x1) > x2 ? 0 : (x2 - x1)));
  uint64_t dy = (((y2 - y1) > y2 ? 0 : (y2 - y1)));
  return ((dx * dx) + (dy * dy));
}

uint64_t
RecordFieldPatterns::bounded_range(const RecordFieldPatterns::Bounded &b) {
  uint64_t l = b.lo;
  uint64_t h = b.hi;
  uint64_t m = b.mid;
  return ((((h - l) > h ? 0 : (h - l))) + m);
}

uint64_t
RecordFieldPatterns::sum_px(const List<RecordFieldPatterns::Point> &points) {
  return points.template fold_left<uint64_t>(
      [](uint64_t acc, const RecordFieldPatterns::Point &p) {
        return (acc + p.px);
      },
      UINT64_C(0));
}

List<uint64_t>
RecordFieldPatterns::map_py(const List<RecordFieldPatterns::Point> &points) {
  return points.template map<uint64_t>(
      [](const RecordFieldPatterns::Point &p) { return p.py; });
}

RecordFieldPatterns::Point
RecordFieldPatterns::swap(const RecordFieldPatterns::Point &p) {
  uint64_t x = p.px;
  uint64_t y = p.py;
  return Point{y, x};
}

RecordFieldPatterns::Point
RecordFieldPatterns::double_swap(const RecordFieldPatterns::Point &p) {
  return swap(swap(p));
}

uint64_t
RecordFieldPatterns::get_count(const RecordFieldPatterns::Container &c) {
  return c.count;
}
