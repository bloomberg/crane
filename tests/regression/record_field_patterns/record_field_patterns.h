#ifndef INCLUDED_RECORD_FIELD_PATTERNS
#define INCLUDED_RECORD_FIELD_PATTERNS

#include <any>
#include <concepts>
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
  if constexpr (requires { x->clone(); }) {
    return x ? std::make_shared<T>(x->clone()) : nullptr;
  } else {
    return x;
  }
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

  template <typename T1, MapsTo<T1, T1, t_A> F0>
  T1 fold_left(F0 &&f, const T1 a0) const {
    auto &&_sv = *(this);
    if (std::holds_alternative<typename List<t_A>::Nil>(_sv.v())) {
      return a0;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<t_A>::Cons>(_sv.v());
      return (*(d_a1)).template fold_left<T1>(f, f(a0, d_a0));
    }
  }

  template <typename T1, MapsTo<T1, t_A> F0>
  __attribute__((pure)) List<T1> map(F0 &&f) const {
    auto &&_sv = *(this);
    if (std::holds_alternative<typename List<t_A>::Nil>(_sv.v())) {
      return List<T1>::nil();
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<t_A>::Cons>(_sv.v());
      return List<T1>::cons(f(d_a0), (*(d_a1)).template map<T1>(f));
    }
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

    __attribute__((pure)) Point *operator->() { return this; }

    __attribute__((pure)) const Point *operator->() const { return this; }
  };

  __attribute__((pure)) static unsigned int classify_point(const Point &p);
  __attribute__((pure)) static unsigned int zero_x(const Point &p);

  template <typename T1> static T1 identity(const T1 x) { return x; }

  /// Apply a polymorphic function to a record — the record type flows
  /// through a type variable.
  __attribute__((pure)) static Point id_point(const Point &_x0);

  /// Polymorphic projection: the match happens inside a polymorphic context
  /// where the scrutinee's type might not be Tglob.
  template <typename T1, typename T2>
  static T1 generic_first(const std::pair<T1, T2> &_x0) {
    return _x0.first;
  }

  __attribute__((pure)) static std::pair<unsigned int, unsigned int>
  point_pair(const Point &p);
  __attribute__((pure)) static unsigned int first_coord(
      const Point
          &p); /// Record whose field default depends on the section variable.

  struct ScaledPoint {
    unsigned int sp_x;
    unsigned int sp_y;

    __attribute__((pure)) ScaledPoint *operator->() { return this; }

    __attribute__((pure)) const ScaledPoint *operator->() const { return this; }
  };

  __attribute__((pure)) static unsigned int
  scaled_sum(const unsigned int &scale, const ScaledPoint &sp);
  /// After section closing, scaled_sum is parameterized by scale : nat.
  /// The record type itself is NOT parameterized (scale is only used in
  /// the function body), but the function signature changes.
  static inline const unsigned int test_labeled =
      scaled_sum(3u, ScaledPoint{10u, 20u});

  struct PointImpl {
    using R = Point;
    __attribute__((pure)) static Point mk(unsigned int x, unsigned int x0);
    __attribute__((pure)) static unsigned int get_x(const Point &p);
    __attribute__((pure)) static unsigned int get_y(const Point &p);
  };

  template <HasRecord M> struct UseRecord {
    __attribute__((pure)) static unsigned int
    sum_fields(const typename M::R r) {
      return (M::get_x(r) + M::get_y(r));
    }
  };

  using UR = UseRecord<PointImpl>;
  static inline const unsigned int test_functor =
      UR::sum_fields(Point{100u, 200u});

  struct Segment {
    Point seg_start;
    Point seg_end;

    __attribute__((pure)) Segment *operator->() { return this; }

    __attribute__((pure)) const Segment *operator->() const { return this; }
  };

  __attribute__((pure)) static unsigned int segment_length_sq(const Segment &s);

  struct Bounded {
    unsigned int lo;
    unsigned int hi;
    unsigned int mid;

    __attribute__((pure)) Bounded *operator->() { return this; }

    __attribute__((pure)) const Bounded *operator->() const { return this; }
  };

  __attribute__((pure)) static unsigned int bounded_range(const Bounded &b);
  __attribute__((pure)) static unsigned int sum_px(const List<Point> &points);
  __attribute__((pure)) static List<unsigned int>
  map_py(const List<Point> &points);
  __attribute__((pure)) static Point swap(const Point &p);
  __attribute__((pure)) static Point double_swap(const Point &p);

  struct Container {
    std::any elem;
    unsigned int count;

    __attribute__((pure)) Container *operator->() { return this; }

    __attribute__((pure)) const Container *operator->() const { return this; }
  };

  using elem_type = std::any;
  __attribute__((pure)) static unsigned int get_count(const Container &c);
  static inline const unsigned int test_container =
      get_count(Container{42u, 5u});
  static inline const unsigned int test_origin = classify_point(Point{0u, 0u});
  static inline const unsigned int test_y_axis = classify_point(Point{0u, 5u});
  static inline const unsigned int test_x_axis = classify_point(Point{3u, 0u});
  static inline const unsigned int test_general = classify_point(Point{3u, 4u});
  static inline const unsigned int test_zero_x = zero_x(Point{0u, 42u});
  static inline const unsigned int test_nonzero = zero_x(Point{5u, 10u});
  static inline const Point test_id = id_point(Point{99u, 1u});
  static inline const unsigned int test_seg =
      segment_length_sq(Segment{Point{1u, 2u}, Point{4u, 6u}});
  static inline const unsigned int test_sum = sum_px(List<Point>::cons(
      Point{10u, 0u},
      List<Point>::cons(
          Point{20u, 0u},
          List<Point>::cons(Point{30u, 0u}, List<Point>::nil()))));
  static inline const List<unsigned int> test_map = map_py(List<Point>::cons(
      Point{0u, 1u},
      List<Point>::cons(Point{0u, 2u},
                        List<Point>::cons(Point{0u, 3u}, List<Point>::nil()))));
  static inline const Point test_swap = swap(Point{3u, 7u});
};

#endif // INCLUDED_RECORD_FIELD_PATTERNS
