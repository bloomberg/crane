#ifndef INCLUDED_POLYGON_WINDING_AREA_TRACE
#define INCLUDED_POLYGON_WINDING_AREA_TRACE

#include <algorithm>
#include <any>
#include <cassert>
#include <crane_real.h>
#include <cstdint>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

template <typename t_A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    t_A d_a0;
    std::shared_ptr<List<t_A>> d_a1;
  };

  using variant_t = std::variant<Nil, Cons>;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  explicit List(Nil _v) : d_v_(std::move(_v)) {}

  explicit List(Cons _v) : d_v_(std::move(_v)) {}

  static std::shared_ptr<List<t_A>> nil() {
    return std::make_shared<List<t_A>>(Nil{});
  }

  static std::shared_ptr<List<t_A>> cons(t_A a0,
                                         const std::shared_ptr<List<t_A>> &a1) {
    return std::make_shared<List<t_A>>(Cons{std::move(a0), a1});
  }

  static std::shared_ptr<List<t_A>> cons(t_A a0,
                                         std::shared_ptr<List<t_A>> &&a1) {
    return std::make_shared<List<t_A>>(Cons{std::move(a0), std::move(a1)});
  }

  static std::unique_ptr<List<t_A>> nil_uptr() {
    return std::make_unique<List<t_A>>(Nil{});
  }

  static std::unique_ptr<List<t_A>>
  cons_uptr(t_A a0, const std::shared_ptr<List<t_A>> &a1) {
    return std::make_unique<List<t_A>>(Cons{std::move(a0), a1});
  }

  static std::unique_ptr<List<t_A>> cons_uptr(t_A a0,
                                              std::shared_ptr<List<t_A>> &&a1) {
    return std::make_unique<List<t_A>>(Cons{std::move(a0), std::move(a1)});
  }

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }

  t_A nth(const unsigned int n, const t_A default0) const {
    if (n <= 0) {
      return std::visit(
          Overloaded{[&](const typename List<t_A>::Nil _args) -> t_A {
                       return default0;
                     },
                     [](const typename List<t_A>::Cons _args) -> t_A {
                       return _args.d_a0;
                     }},
          this->v());
    } else {
      unsigned int m = n - 1;
      return std::visit(
          Overloaded{[&](const typename List<t_A>::Nil _args0) -> t_A {
                       return default0;
                     },
                     [&](const typename List<t_A>::Cons _args0) -> t_A {
                       return _args0.d_a1->nth(m, default0);
                     }},
          this->v());
    }
  }

  __attribute__((pure)) unsigned int length() const {
    return std::visit(
        Overloaded{[](const typename List<t_A>::Nil _args) -> unsigned int {
                     return 0u;
                   },
                   [](const typename List<t_A>::Cons _args) -> unsigned int {
                     return (_args.d_a1->length() + 1);
                   }},
        this->v());
  }
};

struct PeanoNat {
  __attribute__((pure)) static unsigned int sub(const unsigned int n,
                                                const unsigned int m);
  __attribute__((pure)) static std::pair<unsigned int, unsigned int>
  divmod(const unsigned int x, const unsigned int y, const unsigned int q,
         const unsigned int u);
  __attribute__((pure)) static unsigned int modulo(const unsigned int x,
                                                   const unsigned int y);
};

struct Pos {
  template <typename T1, MapsTo<T1, T1> F0>
  static T1 iter(F0 &&f, const T1 x, const unsigned int n) {
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
  __attribute__((pure)) static int64_t pow_pos(const int64_t z,
                                               const unsigned int _x0);
};

struct Q {
  int64_t Qnum;
  unsigned int Qden;
};

struct Rdefinitions {
  __attribute__((pure)) static Real Q2R(std::shared_ptr<Q> x);
};

struct PolygonWindingAreaTraceCase {
  struct Point {
    Real phi;
    Real lambda;
  };

  static inline const Real R_earth_default = Rdefinitions::Q2R(std::make_shared<
                                                               Q>(Q{
      static_cast<int64_t>((
          2u *
              (2u *
               (2u *
                (2u *
                 (2u *
                  (2u *
                   (2u *
                        (2u *
                             (2u *
                                  (2u *
                                   (2u *
                                        (2u *
                                             (2u *
                                                  (2u *
                                                       (2u *
                                                            (2u *
                                                             (2u *
                                                              (2u *
                                                               (2u * (2u *
                                                                      (2u * 1u +
                                                                       1u)) +
                                                                1u)))) +
                                                        1u) +
                                                   1u) +
                                              1u) +
                                         1u) +
                                    1u)) +
                              1u) +
                         1u) +
                    1u)))))) +
          1u)),
      (2u *
       (2u *
        (2u * (2u * (2u * (2u * (2u * (2u * (2u * 1u + 1u) + 1u) + 1u) + 1u)) +
               1u))))}));
  static inline const Real R_earth = R_earth_default;
  __attribute__((pure)) static Real hav(const Real theta);
  __attribute__((pure)) static Real distance(const std::shared_ptr<Point> &p1,
                                             const std::shared_ptr<Point> &p2);
  using Polygon = std::shared_ptr<List<std::shared_ptr<Point>>>;

  template <typename T1>
  static T1 nth_cyclic(const T1 default0, const std::shared_ptr<List<T1>> &l,
                       const unsigned int i) {
    return l->nth(PeanoNat::modulo(i, l->length()), default0);
  }

  __attribute__((pure)) static Real lon_diff(const Real lon1, const Real lon2);
  __attribute__((pure)) static Real spherical_shoelace_aux(
      const std::shared_ptr<List<std::shared_ptr<Point>>> &pts,
      const std::shared_ptr<List<std::shared_ptr<Point>>> &all_pts,
      const unsigned int idx);
  __attribute__((pure)) static Real
  spherical_shoelace(const std::shared_ptr<List<std::shared_ptr<Point>>> &pts);
  __attribute__((pure)) static Real spherical_polygon_area(
      const std::shared_ptr<List<std::shared_ptr<Point>>> &poly);
  __attribute__((pure)) static Real distance_to_central_angle(const Real d);
  __attribute__((pure)) static Real
  spherical_cosine_arg(const Real ca, const Real cb, const Real cab);
  __attribute__((pure)) static Real
  law_of_cosines_arg(const Real da, const Real db, const Real dab);
  __attribute__((pure)) static Real
  segment_angle(const std::shared_ptr<Point> &p,
                const std::shared_ptr<Point> &a,
                const std::shared_ptr<Point> &b);
  __attribute__((pure)) static Real
  winding_sum_aux(const std::shared_ptr<Point> &p,
                  const std::shared_ptr<List<std::shared_ptr<Point>>> &pts,
                  const std::shared_ptr<Point> &first);
  __attribute__((pure)) static Real
  winding_sum(const std::shared_ptr<Point> &p,
              const std::shared_ptr<List<std::shared_ptr<Point>>> &poly);
  __attribute__((pure)) static Real
  winding_number(const std::shared_ptr<Point> &p,
                 const std::shared_ptr<List<std::shared_ptr<Point>>> &poly);
  __attribute__((pure)) static bool
  inside_by_winding(const std::shared_ptr<Point> &p,
                    const std::shared_ptr<List<std::shared_ptr<Point>>> &poly);
  __attribute__((pure)) static bool
  nonnegative_area(const std::shared_ptr<List<std::shared_ptr<Point>>> &poly);
  __attribute__((pure)) static bool
  nonnegative_segment_angle(const std::shared_ptr<Point> &p,
                            const std::shared_ptr<Point> &a,
                            const std::shared_ptr<Point> &b);
  __attribute__((pure)) static bool winding_number_gt_half(
      const std::shared_ptr<Point> &p,
      const std::shared_ptr<List<std::shared_ptr<Point>>> &poly);
  static inline const std::shared_ptr<Point> test_triangle_v1 =
      std::make_shared<Point>(
          Point{Real::from_z(INT64_C(0)), Real::from_z(INT64_C(0))});
  static inline const std::shared_ptr<Point> test_triangle_v2 =
      std::make_shared<Point>(Point{Real::from_z(static_cast<int64_t>(1u)),
                                    Real::from_z(INT64_C(0))});
  static inline const std::shared_ptr<Point> test_triangle_v3 =
      std::make_shared<Point>(
          Point{(Real::from_z(static_cast<int64_t>(1u)) /
                 Real::from_z(static_cast<int64_t>((2u * 1u)))),
                Real::from_z(static_cast<int64_t>(1u))});
  static inline const Polygon test_triangle =
      List<std::shared_ptr<Point>>::cons(
          test_triangle_v1,
          List<std::shared_ptr<Point>>::cons(
              test_triangle_v2,
              List<std::shared_ptr<Point>>::cons(
                  test_triangle_v3, List<std::shared_ptr<Point>>::nil())));
  static inline const std::shared_ptr<Point> test_centroid =
      std::make_shared<Point>(
          Point{(Real::from_z(static_cast<int64_t>(1u)) /
                 Real::from_z(static_cast<int64_t>((2u * 1u)))),
                (Real::from_z(static_cast<int64_t>(1u)) /
                 Real::from_z(static_cast<int64_t>((2u * 1u + 1u))))});
  static inline const std::shared_ptr<Point> test_exterior =
      std::make_shared<Point>(
          Point{(Real::from_z(static_cast<int64_t>(1u)) /
                 Real::from_z(static_cast<int64_t>((2u * 1u)))),
                Real::from_z((-static_cast<int64_t>(1u)))});
  __attribute__((pure)) static Polygon test_equatorial_square(const Real delta);
  static inline const Real sample_square_delta =
      (Real::from_z(static_cast<int64_t>(1u)) /
       Real::from_z(static_cast<int64_t>((2u * (2u * (2u * 1u) + 1u)))));
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

#endif // INCLUDED_POLYGON_WINDING_AREA_TRACE
