#pragma once

#include "crane_fn.h"
#include "obj.h"
#include "small_vector.h"
#include <atomic>
#include <crane_real.h>
#include <cstdint>
#include <memory>
#include <stdexcept>
#include <utility>
#include <variant>

template <typename A> struct List;
struct Q;

struct Nat {};

struct Z {
  static int64_t pow_pos(int64_t z, unsigned int x0_);
};

template <typename A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    A a;
    std::shared_ptr<List<A>> l;
  };

  using variant_t = std::variant<Nil, Cons>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  List() {}

  explicit List(Nil _v) : v_(_v) {}

  explicit List(Cons _v) : v_(std::move(_v)) {}

  template <typename CraneU>
  List(const List<CraneU> &_other)
      : v_([&]() -> variant_t {
          if (std::holds_alternative<typename List<CraneU>::Nil>(_other.v())) {
            return Nil{};
          } else {
            const auto &[a, l] =
                std::get<typename List<CraneU>::Cons>(_other.v());
            return Cons{
                [&]() -> A {
                  if constexpr (crane_convertible<A, const CraneU &>) {
                    return crane_convert<A>(a);
                  } else {
                    throw std::logic_error("unreachable: inactive constructor "
                                           "field at this instantiation");
                  }
                }(),
                (l ? std::make_shared<List<A>>(crane_convert<List<A>>(*l))
                   : nullptr)};
          }
        }()) {}

  static List<A> nil() { return List<A>(Nil{}); }

  static List<A> cons(A a, crane::shared_child_slot<List<A>> l) {
    return List<A>(Cons{std::move(a), l.take()});
  }

  // MANIPULATORS
  ~List() {
    // Release the children this node alone owns in a loop, not recursively, so
    // a deep value cannot overflow the stack.
    auto _next = [&](variant_t &_v) -> std::shared_ptr<List<A>> {
      if (auto *_alt = std::get_if<Cons>(&_v)) {
        if (_alt->l && _alt->l.use_count() == 1) {
          std::atomic_thread_fence(std::memory_order_acquire);
          return std::move(_alt->l);
        }
      }
      return nullptr;
    };
    std::shared_ptr<List<A>> _cur = _next(v_mut());
    while (_cur) {
      _cur = _next(_cur->v_mut());
    }
  }

  List(const List &) = default;
  List &operator=(const List &) = default;
  List(List &&) = default;
  List &operator=(List &&) = default;

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  uint64_t length() const {
    const List<A> *_self = this;

    // Explicit stack replaces the non-tail recursion of length: _call frames
    // are pending calls, _after frames resume a caller.
    struct _call {
      const List<A> *_self;
    };

    struct _after_length_in_Cons {};

    using _frame = std::variant<_call, _after_length_in_Cons>;
    uint64_t _result{};
    crane::small_vector<_frame> _stack;
    _stack.emplace_back(_call{_self});
    while (!_stack.empty()) {
      _frame &_popped = _stack.back();
      if (std::holds_alternative<_call>(_popped)) {
        auto _f = std::move(std::get<_call>(_popped));
        _stack.pop_back();
        const List<A> *_self = _f._self;
        auto &&_sv = *_self;
        if (std::holds_alternative<typename List<A>::Nil>(_sv.v())) {
          _result = UINT64_C(0);
        } else {
          const auto &[_, a1] = std::get<typename List<A>::Cons>(_sv.v());
          _stack.emplace_back(_after_length_in_Cons{});
          _stack.emplace_back(_call{crane_raw(a1)});
        }
      } else {
        auto _f = std::move(std::get<_after_length_in_Cons>(_popped));
        _stack.pop_back();
        _result = (_result + 1);
      }
    }
    return _result;
  }
};

struct ListDef {
  template <typename T1>
  static T1 nth(uint64_t n, const List<T1> &l, T1 default0);
};

struct Pos {
  template <typename T1, typename F0>
  static T1 iter(F0 &&f, const T1 &x, unsigned int n) {
    if (n == 1u) {
      return f(x);
    } else if (n % 2u != 0u) {
      unsigned int n_ = (n - 1u) / 2u;
      return f(iter<T1>(f, iter<T1>(f, x, n_), n_));
    } else {
      unsigned int n_ = n / 2u;
      return iter<T1>(f, iter<T1>(f, x, n_), n_);
    }
  }
};

struct Q {
  int64_t Qnum;
  unsigned int Qden;
};

struct Rdefinitions {
  static Real Q2R(const Q &x);
};

struct PolygonWindingAreaTraceCase {
  struct Point {
    Real phi;
    Real lambda;
  };

  static inline const Real R_earth_default =
      Rdefinitions::Q2R(Q{INT64_C(3440065), 1000u});
  [[gnu::used]] static inline const Real R_earth = R_earth_default;
  static Real hav(Real theta);
  static Real distance(const Point &p1, const Point &p2);
  using Polygon = List<Point>;

  template <typename T1>
  static T1 nth_cyclic(T1 default0, const List<T1> &l, uint64_t i) {
    auto _once1 = l.length();
    return ListDef::template nth<T1>((_once1 ? i % _once1 : i), l,
                                     std::move(default0));
  }

  static Real lon_diff(Real lon1, Real lon2);
  static Real spherical_shoelace_aux(const List<Point> &pts,
                                     const List<Point> &all_pts, uint64_t idx);
  static Real spherical_shoelace(const List<Point> &pts);
  static Real spherical_polygon_area(const List<Point> &poly);
  static Real distance_to_central_angle(Real d);
  static Real spherical_cosine_arg(Real ca, Real cb, Real cab);
  static Real law_of_cosines_arg(Real da, Real db, Real dab);
  static Real segment_angle(const Point &p, const Point &a, const Point &b);
  static Real winding_sum_aux(const Point &p, const List<Point> &pts,
                              const Point &first);
  static Real winding_sum(const Point &p, const List<Point> &poly);
  static Real winding_number(const Point &p, const List<Point> &poly);
  static bool inside_by_winding(const Point &p, const List<Point> &poly);
  static bool nonnegative_area(const List<Point> &poly);
  static bool nonnegative_segment_angle(const Point &p, const Point &a,
                                        const Point &b);
  static bool winding_number_gt_half(const Point &p, const List<Point> &poly);
  static inline const Point test_triangle_v1 =
      Point{Real::from_z(INT64_C(0)), Real::from_z(INT64_C(0))};
  static inline const Point test_triangle_v2 =
      Point{Real::from_z(INT64_C(1)), Real::from_z(INT64_C(0))};
  static inline const Point test_triangle_v3 =
      Point{(Real::from_z(INT64_C(1)) / Real::from_z(INT64_C(2))),
            Real::from_z(INT64_C(1))};
  static inline const Polygon test_triangle = List<Point>::cons(
      test_triangle_v1,
      List<Point>::cons(test_triangle_v2,
                        List<Point>::cons(test_triangle_v3,
                                          List<Point>::nil())));
  static inline const Point test_centroid =
      Point{(Real::from_z(INT64_C(1)) / Real::from_z(INT64_C(2))),
            (Real::from_z(INT64_C(1)) / Real::from_z(INT64_C(3)))};
  static inline const Point test_exterior =
      Point{(Real::from_z(INT64_C(1)) / Real::from_z(INT64_C(2))),
            Real::from_z(INT64_C(-1))};
  static Polygon test_equatorial_square(Real delta);
  static inline const Real sample_square_delta =
      (Real::from_z(INT64_C(1)) / Real::from_z(INT64_C(10)));
  static inline const bool sample_centroid_inside =
      inside_by_winding(test_centroid, test_triangle);
  static inline const bool sample_exterior_inside =
      inside_by_winding(test_exterior, test_triangle);
  static inline const bool sample_triangle_area_nonnegative =
      nonnegative_area(test_triangle);
  static inline const bool sample_square_area_nonnegative =
      nonnegative_area(test_equatorial_square(sample_square_delta));
  static inline const bool sample_first_angle_nonnegative =
      nonnegative_segment_angle(test_centroid, test_triangle_v1,
                                test_triangle_v2);
  static inline const bool sample_centroid_winding_gt_half =
      winding_number_gt_half(test_centroid, test_triangle);
};

template <typename T1>
T1 ListDef::nth(uint64_t n, const List<T1> &l, T1 default0) {
  if (n <= 0) {
    if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
      return default0;
    } else {
      const auto &[a0, _] = std::get<typename List<T1>::Cons>(l.v());
      return a0;
    }
  } else {
    uint64_t m = n - 1;
    if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
      return default0;
    } else {
      const auto &[_, a10] = std::get<typename List<T1>::Cons>(l.v());
      return ListDef::template nth<T1>(m, *a10, std::move(default0));
    }
  }
}
