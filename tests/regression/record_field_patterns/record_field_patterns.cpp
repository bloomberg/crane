#include <record_field_patterns.h>

#include <any>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

__attribute__((pure)) unsigned int RecordFieldPatterns::classify_point(
    const std::shared_ptr<RecordFieldPatterns::Point> &p) {
  return [&](void) {
    unsigned int x = p->px;
    unsigned int y = p->py;
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
  }();
}

__attribute__((pure)) unsigned int RecordFieldPatterns::zero_x(
    const std::shared_ptr<RecordFieldPatterns::Point> &p) {
  return [&](void) {
    unsigned int px0 = p->px;
    unsigned int n = p->py;
    if (px0 <= 0) {
      return n;
    } else {
      unsigned int m = px0 - 1;
      return (m + n);
    }
  }();
}

/// Apply a polymorphic function to a record — the record type flows
/// through a type variable.
std::shared_ptr<RecordFieldPatterns::Point> RecordFieldPatterns::id_point(
    const std::shared_ptr<RecordFieldPatterns::Point> &_x0) {
  return identity<std::shared_ptr<RecordFieldPatterns::Point>>(_x0);
}

__attribute__((pure)) std::pair<unsigned int, unsigned int>
RecordFieldPatterns::point_pair(std::shared_ptr<RecordFieldPatterns::Point> p) {
  return std::make_pair(p->px, p->py);
}

__attribute__((pure)) unsigned int RecordFieldPatterns::first_coord(
    const std::shared_ptr<RecordFieldPatterns::Point> &p) {
  return generic_first<unsigned int, unsigned int>(point_pair(p));
}

__attribute__((pure)) unsigned int RecordFieldPatterns::scaled_sum(
    const unsigned int scale,
    const std::shared_ptr<RecordFieldPatterns::ScaledPoint> &sp) {
  return [&](void) {
    unsigned int x = sp->sp_x;
    unsigned int y = sp->sp_y;
    return (scale * (x + y));
  }();
}

std::shared_ptr<RecordFieldPatterns::Point>
RecordFieldPatterns::PointImpl::mk(const unsigned int x,
                                   const unsigned int x0) {
  return std::make_shared<RecordFieldPatterns::Point>(
      Point{std::move(x), std::move(x0)});
}

__attribute__((pure)) unsigned int RecordFieldPatterns::PointImpl::get_x(
    const std::shared_ptr<RecordFieldPatterns::Point> &p) {
  return p->px;
}

__attribute__((pure)) unsigned int RecordFieldPatterns::PointImpl::get_y(
    const std::shared_ptr<RecordFieldPatterns::Point> &p) {
  return p->py;
}

__attribute__((pure)) unsigned int RecordFieldPatterns::segment_length_sq(
    const std::shared_ptr<RecordFieldPatterns::Segment> &s) {
  return [&](void) {
    std::shared_ptr<RecordFieldPatterns::Point> seg_start0 = s->seg_start;
    std::shared_ptr<RecordFieldPatterns::Point> seg_end0 = s->seg_end;
    return [&](void) {
      unsigned int x1 = seg_start0->px;
      unsigned int y1 = seg_start0->py;
      return [&](void) {
        unsigned int x2 = seg_end0->px;
        unsigned int y2 = seg_end0->py;
        unsigned int dx = (((x2 - x1) > x2 ? 0 : (x2 - x1)));
        unsigned int dy = (((y2 - y1) > y2 ? 0 : (y2 - y1)));
        return ((dx * dx) + (dy * dy));
      }();
    }();
  }();
}

__attribute__((pure)) unsigned int RecordFieldPatterns::bounded_range(
    const std::shared_ptr<RecordFieldPatterns::Bounded> &b) {
  return [&](void) {
    unsigned int l = b->lo;
    unsigned int h = b->hi;
    unsigned int m = b->mid;
    return ((((h - l) > h ? 0 : (h - l))) + m);
  }();
}

__attribute__((pure)) unsigned int RecordFieldPatterns::sum_px(
    const std::shared_ptr<List<std::shared_ptr<RecordFieldPatterns::Point>>>
        &points) {
  return points->template fold_left<unsigned int>(
      [](unsigned int acc, std::shared_ptr<RecordFieldPatterns::Point> p) {
        return (acc + p->px);
      },
      0u);
}

std::shared_ptr<List<unsigned int>> RecordFieldPatterns::map_py(
    const std::shared_ptr<List<std::shared_ptr<RecordFieldPatterns::Point>>>
        &points) {
  return points->template map<unsigned int>(
      [](std::shared_ptr<RecordFieldPatterns::Point> p) { return p->py; });
}

std::shared_ptr<RecordFieldPatterns::Point> RecordFieldPatterns::swap(
    const std::shared_ptr<RecordFieldPatterns::Point> &p) {
  return [&](void) {
    unsigned int x = p->px;
    unsigned int y = p->py;
    return std::make_shared<RecordFieldPatterns::Point>(Point{y, x});
  }();
}

std::shared_ptr<RecordFieldPatterns::Point> RecordFieldPatterns::double_swap(
    const std::shared_ptr<RecordFieldPatterns::Point> &p) {
  return swap(swap(p));
}

__attribute__((pure)) unsigned int RecordFieldPatterns::get_count(
    const std::shared_ptr<RecordFieldPatterns::Container> &c) {
  return c->count;
}
