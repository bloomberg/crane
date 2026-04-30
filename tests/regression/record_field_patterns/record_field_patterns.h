#ifndef INCLUDED_RECORD_FIELD_PATTERNS
#define INCLUDED_RECORD_FIELD_PATTERNS

#include <any>
#include <concepts>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

template <typename t_A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    t_A d_a0;
    std::unique_ptr<List<t_A>> d_a1;
  };

  using variant_t = std::variant<Nil, Cons>;

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

  List<t_A> &operator=(const List<t_A> &_other) {
    d_v_ = std::move(_other.clone().d_v_);
    return *this;
  }

  List<t_A> &operator=(List<t_A> &&_other) {
    d_v_ = std::move(_other.d_v_);
    return *this;
  }

  // ACCESSORS
  List<t_A> clone() const {
    List<t_A> _out{};

    struct _CloneFrame {
      const List<t_A> *_src;
      List<t_A> *_dst;
    };

    std::vector<_CloneFrame> _stack{};
    _stack.push_back({this, &_out});
    while (!_stack.empty()) {
      auto _frame = _stack.back();
      _stack.pop_back();
      const List<t_A> *_src = _frame._src;
      List<t_A> *_dst = _frame._dst;
      if (std::holds_alternative<Nil>(_src->v())) {
        _dst->d_v_ = Nil{};
      } else {
        const auto &_alt = std::get<Cons>(_src->v());
        _dst->d_v_ = Cons{_alt.d_a0,
                          _alt.d_a1 ? std::make_unique<List<t_A>>() : nullptr};
        auto &_dst_alt = std::get<Cons>(_dst->d_v_);
        if (_alt.d_a1) {
          _stack.push_back({_alt.d_a1.get(), _dst_alt.d_a1.get()});
        }
      }
    }
    return _out;
  }

  // CREATORS
  template <typename _U> explicit List(const List<_U> &_other) {
    if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
      d_v_ = Nil{};
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<_U>::Cons>(_other.v());
      d_v_ =
          Cons{t_A(d_a0), d_a1 ? std::make_unique<List<t_A>>(*d_a1) : nullptr};
    }
  }

  static List<t_A> nil() { return List(Nil{}); }

  static List<t_A> cons(t_A a0, List<t_A> a1) {
    return List(
        Cons{std::move(a0), std::make_unique<List<t_A>>(std::move(a1))});
  }

  // MANIPULATORS
  ~List() {
    std::vector<std::unique_ptr<List<t_A>>> _stack{};
    auto _drain = [&](List<t_A> &_node) {
      if (std::holds_alternative<Cons>(_node.d_v_)) {
        auto &_alt = std::get<Cons>(_node.d_v_);
        if (_alt.d_a1) {
          _stack.push_back(std::move(_alt.d_a1));
        }
      }
    };
    _drain(*this);
    while (!_stack.empty()) {
      auto _node = std::move(_stack.back());
      _stack.pop_back();
      if (_node) {
        _drain(*_node);
      }
    }
  }

  inline variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  const variant_t &v() const { return d_v_; }

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

  template <typename T1, MapsTo<T1, t_A> F0> List<T1> map(F0 &&f) const {
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

    // ACCESSORS
    Point clone() const { return Point{(*(this)).px, (*(this)).py}; }
  };

  static unsigned int classify_point(const Point &p);
  static unsigned int zero_x(const Point &p);

  template <typename T1> static T1 identity(const T1 x) { return x; }

  /// Apply a polymorphic function to a record — the record type flows
  /// through a type variable.
  static Point id_point(const Point &_x0);

  /// Polymorphic projection: the match happens inside a polymorphic context
  /// where the scrutinee's type might not be Tglob.
  template <typename T1, typename T2>
  static T1 generic_first(const std::pair<T1, T2> &_x0) {
    return _x0.first;
  }

  static std::pair<unsigned int, unsigned int> point_pair(const Point &p);
  static unsigned int first_coord(const Point &p);

  /// Record whose field default depends on the section variable.
  struct ScaledPoint {
    unsigned int sp_x;
    unsigned int sp_y;

    // ACCESSORS
    ScaledPoint clone() const {
      return ScaledPoint{(*(this)).sp_x, (*(this)).sp_y};
    }
  };

  static unsigned int scaled_sum(const unsigned int &scale,
                                 const ScaledPoint &sp);
  /// After section closing, scaled_sum is parameterized by scale : nat.
  /// The record type itself is NOT parameterized (scale is only used in
  /// the function body), but the function signature changes.
  static inline const unsigned int test_labeled =
      scaled_sum(3u, ScaledPoint{10u, 20u});

  struct PointImpl {
    using R = Point;
    static Point mk(unsigned int x, unsigned int x0);
    static unsigned int get_x(const Point &p);
    static unsigned int get_y(const Point &p);
  };

  template <HasRecord M> struct UseRecord {
    static unsigned int sum_fields(const typename M::R r) {
      return (M::get_x(r) + M::get_y(r));
    }
  };

  using UR = UseRecord<PointImpl>;
  static inline const unsigned int test_functor =
      UR::sum_fields(Point{100u, 200u});

  struct Segment {
    Point seg_start;
    Point seg_end;

    // ACCESSORS
    Segment clone() const {
      return Segment{(*(this)).seg_start.clone(), (*(this)).seg_end.clone()};
    }
  };

  static unsigned int segment_length_sq(const Segment &s);

  struct Bounded {
    unsigned int lo;
    unsigned int hi;
    unsigned int mid;

    // ACCESSORS
    Bounded clone() const {
      return Bounded{(*(this)).lo, (*(this)).hi, (*(this)).mid};
    }
  };

  static unsigned int bounded_range(const Bounded &b);
  static unsigned int sum_px(const List<Point> &points);
  static List<unsigned int> map_py(const List<Point> &points);
  static Point swap(const Point &p);
  static Point double_swap(const Point &p);

  struct Container {
    std::any elem;
    unsigned int count;

    // ACCESSORS
    Container clone() const {
      return Container{(*(this)).elem, (*(this)).count};
    }
  };

  using elem_type = std::any;
  static unsigned int get_count(const Container &c);
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
