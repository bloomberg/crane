#ifndef INCLUDED_RECORD_FIELD_PATTERNS
#define INCLUDED_RECORD_FIELD_PATTERNS

#include <algorithm>
#include <any>
#include <cassert>
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

  template <typename T1, MapsTo<T1, T1, t_A> F0>
  T1 fold_left(F0 &&f, const T1 a0) const {
    return std::visit(
        Overloaded{
            [&](const typename List<t_A>::Nil _args) -> T1 { return a0; },
            [&](const typename List<t_A>::Cons _args) -> T1 {
              return _args.d_a1->template fold_left<T1>(f, f(a0, _args.d_a0));
            }},
        this->v());
  }

  template <typename T1, MapsTo<T1, t_A> F0>
  std::shared_ptr<List<T1>> map(F0 &&f) const {
    return std::visit(
        Overloaded{[](const typename List<t_A>::Nil _args)
                       -> std::shared_ptr<List<T1>> { return List<T1>::nil(); },
                   [&](const typename List<t_A>::Cons _args)
                       -> std::shared_ptr<List<T1>> {
                     return List<T1>::cons(f(_args.d_a0),
                                           _args.d_a1->template map<T1>(f));
                   }},
        this->v());
  }
};

template <typename M>
concept HasRecord = requires {
  typename M::R;
  {
    M::mk(std::declval<unsigned int>(), std::declval<unsigned int>())
  } -> std::same_as<typename M::R>;
  { M::get_x(std::declval<typename M::R>()) } -> std::same_as<unsigned int>;
  { M::get_y(std::declval<typename M::R>()) } -> std::same_as<unsigned int>;
};

struct RecordFieldPatterns {
  struct Point {
    unsigned int px;
    unsigned int py;
  };

  __attribute__((pure)) static unsigned int
  classify_point(const std::shared_ptr<Point> &p);
  __attribute__((pure)) static unsigned int
  zero_x(const std::shared_ptr<Point> &p);

  template <typename T1> static T1 identity(const T1 x) { return x; }

  /// Apply a polymorphic function to a record — the record type flows
  /// through a type variable.
  static std::shared_ptr<Point> id_point(const std::shared_ptr<Point> &_x0);

  /// Polymorphic projection: the match happens inside a polymorphic context
  /// where the scrutinee's type might not be Tglob.
  template <typename T1, typename T2>
  static T1 generic_first(const std::pair<T1, T2> _x0) {
    return _x0.first;
  }

  __attribute__((pure)) static std::pair<unsigned int, unsigned int>
  point_pair(std::shared_ptr<Point> p);
  __attribute__((pure)) static unsigned int first_coord(
      const std::shared_ptr<Point>
          &p); /// Record whose field default depends on the section variable.

  struct ScaledPoint {
    unsigned int sp_x;
    unsigned int sp_y;
  };

  __attribute__((pure)) static unsigned int
  scaled_sum(const unsigned int scale, const std::shared_ptr<ScaledPoint> &sp);
  /// After section closing, scaled_sum is parameterized by scale : nat.
  /// The record type itself is NOT parameterized (scale is only used in
  /// the function body), but the function signature changes.
  static inline const unsigned int test_labeled =
      scaled_sum(3u, std::make_shared<ScaledPoint>(ScaledPoint{10u, 20u}));

  struct PointImpl {
    using R = std::shared_ptr<Point>;
    static std::shared_ptr<Point> mk(const unsigned int x,
                                     const unsigned int x0);
    __attribute__((pure)) static unsigned int
    get_x(const std::shared_ptr<Point> &p);
    __attribute__((pure)) static unsigned int
    get_y(const std::shared_ptr<Point> &p);
  };

  template <HasRecord M> struct UseRecord {
    __attribute__((pure)) static unsigned int
    sum_fields(const typename M::R r) {
      return (M::get_x(r) + M::get_y(r));
    }
  };

  using UR = UseRecord<PointImpl>;
  static inline const unsigned int test_functor =
      UR::sum_fields(std::make_shared<Point>(Point{100u, 200u}));

  struct Segment {
    std::shared_ptr<Point> seg_start;
    std::shared_ptr<Point> seg_end;
  };

  __attribute__((pure)) static unsigned int
  segment_length_sq(const std::shared_ptr<Segment> &s);

  struct Bounded {
    unsigned int lo;
    unsigned int hi;
    unsigned int mid;
  };

  __attribute__((pure)) static unsigned int
  bounded_range(const std::shared_ptr<Bounded> &b);
  __attribute__((pure)) static unsigned int
  sum_px(const std::shared_ptr<List<std::shared_ptr<Point>>> &points);
  static std::shared_ptr<List<unsigned int>>
  map_py(const std::shared_ptr<List<std::shared_ptr<Point>>> &points);
  static std::shared_ptr<Point> swap(const std::shared_ptr<Point> &p);
  static std::shared_ptr<Point> double_swap(const std::shared_ptr<Point> &p);

  struct Container {
    std::any elem;
    unsigned int count;
  };

  using elem_type = std::any;
  __attribute__((pure)) static unsigned int
  get_count(const std::shared_ptr<Container> &c);
  static inline const unsigned int test_container =
      get_count(std::make_shared<Container>(Container{42u, 5u}));
  static inline const unsigned int test_origin =
      classify_point(std::make_shared<Point>(Point{0u, 0u}));
  static inline const unsigned int test_y_axis =
      classify_point(std::make_shared<Point>(Point{0u, 5u}));
  static inline const unsigned int test_x_axis =
      classify_point(std::make_shared<Point>(Point{3u, 0u}));
  static inline const unsigned int test_general =
      classify_point(std::make_shared<Point>(Point{3u, 4u}));
  static inline const unsigned int test_zero_x =
      zero_x(std::make_shared<Point>(Point{0u, 42u}));
  static inline const unsigned int test_nonzero =
      zero_x(std::make_shared<Point>(Point{5u, 10u}));
  static inline const std::shared_ptr<Point> test_id =
      id_point(std::make_shared<Point>(Point{99u, 1u}));
  static inline const unsigned int test_seg =
      segment_length_sq(std::make_shared<Segment>(
          Segment{std::make_shared<Point>(Point{1u, 2u}),
                  std::make_shared<Point>(Point{4u, 6u})}));
  static inline const unsigned int test_sum =
      sum_px(List<std::shared_ptr<Point>>::cons(
          std::make_shared<Point>(Point{10u, 0u}),
          List<std::shared_ptr<Point>>::cons(
              std::make_shared<Point>(Point{20u, 0u}),
              List<std::shared_ptr<Point>>::cons(
                  std::make_shared<Point>(Point{30u, 0u}),
                  List<std::shared_ptr<Point>>::nil()))));
  static inline const std::shared_ptr<List<unsigned int>> test_map =
      map_py(List<std::shared_ptr<Point>>::cons(
          std::make_shared<Point>(Point{0u, 1u}),
          List<std::shared_ptr<Point>>::cons(
              std::make_shared<Point>(Point{0u, 2u}),
              List<std::shared_ptr<Point>>::cons(
                  std::make_shared<Point>(Point{0u, 3u}),
                  List<std::shared_ptr<Point>>::nil()))));
  static inline const std::shared_ptr<Point> test_swap =
      swap(std::make_shared<Point>(Point{3u, 7u}));
};

#endif // INCLUDED_RECORD_FIELD_PATTERNS
