#include <record_field_patterns.h>

#include <any>
#include <concepts>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

__attribute__((pure)) unsigned int
RecordFieldPatterns::classify_point(const RecordFieldPatterns::Point &p) {
  unsigned int x = p.px;
  unsigned int y = p.py;
  if (x <= 0) {
    if (y <= 0) {
      return 0u;
    } else {
      unsigned int _x = y - 1;
      return 1u;
    }
  } else {
    unsigned int _x = x - 1;
    if (y <= 0) {
      return 2u;
    } else {
      unsigned int _x0 = y - 1;
      return (x + y);
    }
  }
}

__attribute__((pure)) unsigned int
RecordFieldPatterns::zero_x(const RecordFieldPatterns::Point &p) {
  unsigned int px0 = p.px;
  unsigned int n = p.py;
  if (px0 <= 0) {
    return n;
  } else {
    unsigned int m = px0 - 1;
    return (m + n);
  }
}

/// Apply a polymorphic function to a record — the record type flows
/// through a type variable.
__attribute__((pure)) RecordFieldPatterns::Point
RecordFieldPatterns::id_point(const RecordFieldPatterns::Point &_x0) {
  return identity<RecordFieldPatterns::Point>(_x0);
}

__attribute__((pure)) std::pair<unsigned int, unsigned int>
RecordFieldPatterns::point_pair(const RecordFieldPatterns::Point &p) {
  return std::make_pair(p.px, p.py);
}

__attribute__((pure)) unsigned int
RecordFieldPatterns::first_coord(const RecordFieldPatterns::Point &p) {
  return generic_first<unsigned int, unsigned int>(point_pair(p));
}

__attribute__((pure)) unsigned int
RecordFieldPatterns::scaled_sum(const unsigned int &scale,
                                const RecordFieldPatterns::ScaledPoint &sp) {
  unsigned int x = sp.sp_x;
  unsigned int y = sp.sp_y;
  return (scale * (x + y));
}

__attribute__((pure)) RecordFieldPatterns::Point
RecordFieldPatterns::PointImpl::mk(unsigned int x, unsigned int x0) {
  return Point{x, x0};
}

__attribute__((pure)) unsigned int
RecordFieldPatterns::PointImpl::get_x(const RecordFieldPatterns::Point &p) {
  return p.px;
}

__attribute__((pure)) unsigned int
RecordFieldPatterns::PointImpl::get_y(const RecordFieldPatterns::Point &p) {
  return p.py;
}

__attribute__((pure)) unsigned int
RecordFieldPatterns::segment_length_sq(const RecordFieldPatterns::Segment &s) {
  RecordFieldPatterns::Point seg_start0 = s.seg_start;
  RecordFieldPatterns::Point seg_end0 = s.seg_end;
  unsigned int x1 = seg_start0.px;
  unsigned int y1 = seg_start0.py;
  unsigned int x2 = seg_end0.px;
  unsigned int y2 = seg_end0.py;
  unsigned int dx = (((x2 - x1) > x2 ? 0 : (x2 - x1)));
  unsigned int dy = (((y2 - y1) > y2 ? 0 : (y2 - y1)));
  return ((dx * dx) + (dy * dy));
}

__attribute__((pure)) unsigned int
RecordFieldPatterns::bounded_range(const RecordFieldPatterns::Bounded &b) {
  unsigned int l = b.lo;
  unsigned int h = b.hi;
  unsigned int m = b.mid;
  return ((((h - l) > h ? 0 : (h - l))) + m);
}

__attribute__((pure)) unsigned int
RecordFieldPatterns::sum_px(const List<RecordFieldPatterns::Point> &points) {
  return points.template fold_left<unsigned int>(
      [](const unsigned int &acc, const RecordFieldPatterns::Point &p) {
        return (acc + p.px);
      },
      0u);
}

__attribute__((pure)) List<unsigned int>
RecordFieldPatterns::map_py(const List<RecordFieldPatterns::Point> &points) {
  return points.template map<unsigned int>(
      [](const RecordFieldPatterns::Point &p) { return p.py; });
}

__attribute__((pure)) RecordFieldPatterns::Point
RecordFieldPatterns::swap(const RecordFieldPatterns::Point &p) {
  unsigned int x = p.px;
  unsigned int y = p.py;
  return Point{y, x};
}

__attribute__((pure)) RecordFieldPatterns::Point
RecordFieldPatterns::double_swap(const RecordFieldPatterns::Point &p) {
  return swap(swap(p));
}

__attribute__((pure)) unsigned int
RecordFieldPatterns::get_count(const RecordFieldPatterns::Container &c) {
  return c.count;
}
