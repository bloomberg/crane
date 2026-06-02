#ifndef INCLUDED_POLYGON_WINDING_AREA_TRACE
#define INCLUDED_POLYGON_WINDING_AREA_TRACE

#include <any>
#include <crane_real.h>
#include <cstdint>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

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

  template <typename _U> explicit List(const List<_U> &_other) {
    if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
      this->v_ = Nil{};
    } else {
      const auto &[a, l] = std::get<typename List<_U>::Cons>(_other.v());
      this->v_ = Cons{
          [&]() -> A {
            if constexpr (std::is_same_v<_U, std::any>) {
              if (a.type() == typeid(A))
                return std::any_cast<A>(a);
              if constexpr (requires {
                              typename A::first_type;
                              typename A::second_type;
                            }) {
                const auto &[_k, _v] =
                    std::any_cast<std::pair<std::any, std::any>>(a);
                return A{[&]() -> typename A::first_type {
                           if constexpr (std::is_same_v<typename A::first_type,
                                                        std::any>)
                             return _k;
                           else
                             return std::any_cast<typename A::first_type>(_k);
                         }(),
                         [&]() -> typename A::second_type {
                           if constexpr (std::is_same_v<typename A::second_type,
                                                        std::any>)
                             return _v;
                           else
                             return std::any_cast<typename A::second_type>(_v);
                         }()};
              }
              return std::any_cast<A>(a);
            } else
              return A(a);
          }(),
          l ? std::make_shared<List<A>>(*l) : nullptr};
    }
  }

  static List<A> nil() { return List(Nil{}); }

  static List<A> cons(A a, List<A> l) {
    return List(Cons{std::move(a), std::make_shared<List<A>>(std::move(l))});
  }

  // MANIPULATORS
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  uint64_t length() const {
    if (std::holds_alternative<typename List<A>::Nil>(this->v())) {
      return UINT64_C(0);
    } else {
      const auto &[a0, a1] = std::get<typename List<A>::Cons>(this->v());
      return (a1->length() + 1);
    }
  }
};

struct Pos {
  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, T1 &>
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

struct BinInt {
  static int64_t pow_pos(int64_t z, unsigned int _x0);
};

struct ListDef {
  template <typename T1>
  static T1 nth(uint64_t n, const List<T1> &l, T1 default0);
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

  static inline const Real R_earth_default = Rdefinitions::Q2R(Q{
      INT64_C(3440065),
      (2u *
       (2u *
        (2u * (2u * (2u * (2u * (2u * (2u * (2u * 1u + 1u) + 1u) + 1u) + 1u)) +
               1u))))});
  static inline const Real R_earth = R_earth_default;
  static Real hav(Real theta);
  static Real distance(const Point &p1, const Point &p2);
  using Polygon = List<Point>;

  template <typename T1>
  static T1 nth_cyclic(const T1 &default0, const List<T1> &l, uint64_t i) {
    return ListDef::template nth<T1>((l.length() ? i % l.length() : i), l,
                                     default0);
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
      List<Point>::cons(
          test_triangle_v2,
          List<Point>::cons(test_triangle_v3, List<Point>::nil())));
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
      const auto &[a0, a1] = std::get<typename List<T1>::Cons>(l.v());
      return a0;
    }
  } else {
    uint64_t m = n - 1;
    if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
      return default0;
    } else {
      const auto &[a00, a10] = std::get<typename List<T1>::Cons>(l.v());
      return ListDef::template nth<T1>(m, *a10, default0);
    }
  }
}

#endif // INCLUDED_POLYGON_WINDING_AREA_TRACE
