#ifndef INCLUDED_POLYGON_WINDING_AREA_TRACE
#define INCLUDED_POLYGON_WINDING_AREA_TRACE

#include <crane_real.h>
#include <cstdint>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

template <typename T> struct is_unique_ptr : std::false_type {};

template <typename T>
struct is_unique_ptr<std::unique_ptr<T>> : std::true_type {
  using element_type = T;
};

template <typename T> struct is_shared_ptr : std::false_type {};

template <typename T>
struct is_shared_ptr<std::shared_ptr<T>> : std::true_type {
  using element_type = T;
};

template <typename T> auto clone_value(const T &x) { return x; }

template <typename T>
std::unique_ptr<T> clone_value(const std::unique_ptr<T> &x) {
  return x ? std::make_unique<T>(x->clone()) : nullptr;
}

template <typename T>
std::shared_ptr<T> clone_value(const std::shared_ptr<T> &x) {
  return x ? std::make_shared<T>(x->clone()) : nullptr;
}

template <typename Target, typename Source>
Target clone_as_value(const Source &x) {
  using TargetBare = std::remove_cvref_t<Target>;
  using SourceBare = std::remove_cvref_t<Source>;
  if constexpr (is_unique_ptr<TargetBare>::value) {
    using Inner = typename is_unique_ptr<TargetBare>::element_type;
    if constexpr (is_unique_ptr<SourceBare>::value) {
      using SourceInner = typename is_unique_ptr<SourceBare>::element_type;
      if (!x)
        return nullptr;
      if constexpr (std::is_same_v<Inner, SourceInner>) {
        return clone_value(x);
      } else if constexpr (requires {
                             typename Inner::crane_element_type;
                             x->template clone_as<
                                 typename Inner::crane_element_type>();
                           }) {
        return std::make_unique<Inner>(
            x->template clone_as<typename Inner::crane_element_type>());
      } else if constexpr (requires { x->template clone_as<Inner>(); }) {
        return std::make_unique<Inner>(x->template clone_as<Inner>());
      } else {
        return std::make_unique<Inner>(x->clone());
      }
    } else {
      if constexpr (std::is_same_v<Inner, SourceBare>) {
        return std::make_unique<Inner>(x.clone());
      } else if constexpr (requires { x.template clone_as<Inner>(); }) {
        return std::make_unique<Inner>(x.template clone_as<Inner>());
      } else {
        return std::make_unique<Inner>(x.clone());
      }
    }
  } else if constexpr (is_shared_ptr<TargetBare>::value) {
    using Inner = typename is_shared_ptr<TargetBare>::element_type;
    if constexpr (is_shared_ptr<SourceBare>::value) {
      using SourceInner = typename is_shared_ptr<SourceBare>::element_type;
      if (!x)
        return nullptr;
      if constexpr (std::is_same_v<Inner, SourceInner>) {
        return clone_value(x);
      } else if constexpr (requires { x->template clone_as<Inner>(); }) {
        return std::make_shared<Inner>(x->template clone_as<Inner>());
      } else {
        return std::make_shared<Inner>(x->clone());
      }
    } else if constexpr (is_unique_ptr<SourceBare>::value) {
      if (!x)
        return nullptr;
      if constexpr (requires { x->template clone_as<Inner>(); }) {
        return std::make_shared<Inner>(x->template clone_as<Inner>());
      } else {
        return std::make_shared<Inner>(x->clone());
      }
    } else {
      if constexpr (std::is_same_v<Inner, SourceBare>) {
        return std::make_shared<Inner>(x.clone());
      } else if constexpr (requires { x.template clone_as<Inner>(); }) {
        return std::make_shared<Inner>(x.template clone_as<Inner>());
      } else {
        return std::make_shared<Inner>(x.clone());
      }
    }
  } else if constexpr (std::is_same_v<TargetBare, SourceBare>) {
    return clone_value(x);
  } else if constexpr (is_unique_ptr<SourceBare>::value) {
    using SourceInner = typename is_unique_ptr<SourceBare>::element_type;
    if constexpr (std::is_same_v<TargetBare, SourceInner>) {
      return x ? x->clone() : Target{};
    } else if constexpr (requires { x->template clone_as<TargetBare>(); }) {
      return x->template clone_as<TargetBare>();
    } else {
      return Target(*x);
    }
  } else if constexpr (is_shared_ptr<SourceBare>::value) {
    using SourceInner = typename is_shared_ptr<SourceBare>::element_type;
    if constexpr (std::is_same_v<TargetBare, SourceInner>) {
      return x ? x->clone() : Target{};
    } else if constexpr (requires { x->template clone_as<TargetBare>(); }) {
      return x->template clone_as<TargetBare>();
    } else {
      return Target(*x);
    }
  } else if constexpr (requires {
                         typename TargetBare::crane_element_type;
                         x.template clone_as<
                             typename TargetBare::crane_element_type>();
                       }) {
    return x.template clone_as<typename TargetBare::crane_element_type>();
  } else if constexpr (requires { x.template clone_as<TargetBare>(); }) {
    return x.template clone_as<TargetBare>();
  } else {
    return Target(x);
  }
}

template <typename t_A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    t_A d_a0;
    std::unique_ptr<List<t_A>> d_a1;
  };

  using variant_t = std::variant<Nil, Cons>;
  using crane_element_type = t_A;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  List() {}

  explicit List(Nil _v) : d_v_(_v) {}

  explicit List(Cons _v) : d_v_(std::move(_v)) {}

  List(const List<t_A> &_other) : d_v_(std::move(_other.clone().d_v_)) {}

  List(List<t_A> &&_other) : d_v_(std::move(_other.d_v_)) {}

  __attribute__((pure)) List<t_A> &operator=(const List<t_A> &_other) {
    d_v_ = std::move(_other.clone().d_v_);
    return *this;
  }

  __attribute__((pure)) List<t_A> &operator=(List<t_A> &&_other) {
    d_v_ = std::move(_other.d_v_);
    return *this;
  }

  // ACCESSORS
  __attribute__((pure)) List<t_A> clone() const {
    auto &&_sv = *(this);
    if (std::holds_alternative<Nil>(_sv.v())) {
      return List<t_A>(Nil{});
    } else {
      const auto &[d_a0, d_a1] = std::get<Cons>(_sv.v());
      return List<t_A>(Cons{clone_as_value<t_A>(d_a0),
                            clone_as_value<std::unique_ptr<List<t_A>>>(d_a1)});
    }
  }

  template <typename _CloneT0>
  __attribute__((pure)) List<_CloneT0> clone_as() const {
    auto &&_sv = *(this);
    if (std::holds_alternative<Nil>(_sv.v())) {
      return List<_CloneT0>(typename List<_CloneT0>::Nil{});
    } else {
      const auto &[d_a0, d_a1] = std::get<Cons>(_sv.v());
      return List<_CloneT0>(typename List<_CloneT0>::Cons{
          clone_as_value<_CloneT0>(d_a0),
          clone_as_value<std::unique_ptr<List<_CloneT0>>>(d_a1)});
    }
  }

  // CREATORS
  __attribute__((pure)) static List<t_A> nil() { return List(Nil{}); }

  __attribute__((pure)) static List<t_A> cons(t_A a0, const List<t_A> &a1) {
    return List(Cons{std::move(a0), std::make_unique<List<t_A>>(a1.clone())});
  }

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) List<t_A> *operator->() { return this; }

  __attribute__((pure)) const List<t_A> *operator->() const { return this; }

  __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

  __attribute__((pure)) bool operator==(std::nullptr_t) const { return false; }

  // MANIPULATORS
  void reset() { *this = List<t_A>(); }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }

  __attribute__((pure)) unsigned int length() const {
    auto &&_sv = *(this);
    if (std::holds_alternative<typename List<t_A>::Nil>(_sv.v())) {
      return 0u;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<t_A>::Cons>(_sv.v());
      return ((*(d_a1)).length() + 1);
    }
  }
};

struct Pos {
  template <typename T1, MapsTo<T1, T1> F0>
  static T1 iter(F0 &&f, const T1 x, const unsigned int &n) {
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
  __attribute__((pure)) static int64_t pow_pos(const int64_t &z,
                                               unsigned int _x0);
};

struct ListDef {
  template <typename T1>
  static T1 nth(const unsigned int &n, const List<T1> &l, const T1 default0);
};

struct Q {
  int64_t Qnum;
  unsigned int Qden;

  __attribute__((pure)) Q *operator->() { return this; }

  __attribute__((pure)) const Q *operator->() const { return this; }
};

struct Rdefinitions {
  __attribute__((pure)) static Real Q2R(const Q &x);
};

struct PolygonWindingAreaTraceCase {
  struct Point {
    Real phi;
    Real lambda;

    __attribute__((pure)) Point *operator->() { return this; }

    __attribute__((pure)) const Point *operator->() const { return this; }
  };

  static inline const Real R_earth_default = Rdefinitions::Q2R(Q{
      INT64_C(3440065),
      (2u *
       (2u *
        (2u * (2u * (2u * (2u * (2u * (2u * (2u * 1u + 1u) + 1u) + 1u) + 1u)) +
               1u))))});
  static inline const Real R_earth = R_earth_default;
  __attribute__((pure)) static Real hav(const Real theta);
  __attribute__((pure)) static Real distance(const Point &p1, const Point &p2);
  using Polygon = List<Point>;

  template <typename T1>
  static T1 nth_cyclic(const T1 default0, const List<T1> &l,
                       const unsigned int &i) {
    return ListDef::template nth<T1>((l.length() ? i % l.length() : i), l,
                                     default0);
  }

  __attribute__((pure)) static Real lon_diff(const Real lon1, const Real lon2);
  __attribute__((pure)) static Real
  spherical_shoelace_aux(const List<Point> &pts, const List<Point> &all_pts,
                         const unsigned int &idx);
  __attribute__((pure)) static Real spherical_shoelace(const List<Point> &pts);
  __attribute__((pure)) static Real
  spherical_polygon_area(const List<Point> &poly);
  __attribute__((pure)) static Real distance_to_central_angle(const Real d);
  __attribute__((pure)) static Real
  spherical_cosine_arg(const Real ca, const Real cb, const Real cab);
  __attribute__((pure)) static Real
  law_of_cosines_arg(const Real da, const Real db, const Real dab);
  __attribute__((pure)) static Real
  segment_angle(const Point &p, const Point &a, const Point &b);
  __attribute__((pure)) static Real
  winding_sum_aux(const Point &p, const List<Point> &pts, const Point &first);
  __attribute__((pure)) static Real winding_sum(const Point &p,
                                                const List<Point> &poly);
  __attribute__((pure)) static Real winding_number(const Point &p,
                                                   const List<Point> &poly);
  __attribute__((pure)) static bool inside_by_winding(const Point &p,
                                                      const List<Point> &poly);
  __attribute__((pure)) static bool nonnegative_area(const List<Point> &poly);
  __attribute__((pure)) static bool
  nonnegative_segment_angle(const Point &p, const Point &a, const Point &b);
  __attribute__((pure)) static bool
  winding_number_gt_half(const Point &p, const List<Point> &poly);
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
  __attribute__((pure)) static Polygon test_equatorial_square(const Real delta);
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
T1 ListDef::nth(const unsigned int &n, const List<T1> &l, const T1 default0) {
  if (n <= 0) {
    if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
      return default0;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<T1>::Cons>(l.v());
      return d_a0;
    }
  } else {
    unsigned int m = n - 1;
    if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
      return default0;
    } else {
      const auto &[d_a00, d_a10] = std::get<typename List<T1>::Cons>(l.v());
      return ListDef::template nth<T1>(m, *(d_a10), default0);
    }
  }
}

#endif // INCLUDED_POLYGON_WINDING_AREA_TRACE
