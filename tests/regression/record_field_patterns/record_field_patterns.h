#ifndef INCLUDED_RECORD_FIELD_PATTERNS
#define INCLUDED_RECORD_FIELD_PATTERNS

#include <any>
#include <concepts>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

template <typename A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    A a;
    std::unique_ptr<List<A>> l;
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

  List(const List<A> &_other) : v_(std::move(_other.clone().v_)) {}

  List(List<A> &&_other) noexcept : v_(std::move(_other.v_)) {}

  List<A> &operator=(const List<A> &_other) {
    v_ = std::move(_other.clone().v_);
    return *this;
  }

  List<A> &operator=(List<A> &&_other) noexcept {
    v_ = std::move(_other.v_);
    return *this;
  }

  // ACCESSORS
  List<A> clone() const {
    List<A> _out{};

    struct _CloneFrame {
      const List<A> *_src;
      List<A> *_dst;
    };

    std::vector<_CloneFrame> _stack{};
    _stack.reserve(8);
    _stack.push_back({this, &_out});
    while (!_stack.empty()) {
      auto _frame = _stack.back();
      _stack.pop_back();
      const List<A> *_src = _frame._src;
      List<A> *_dst = _frame._dst;
      if (std::holds_alternative<Nil>(_src->v())) {
        _dst->v_ = Nil{};
      } else {
        const auto &_alt = std::get<Cons>(_src->v());
        _dst->v_ = Cons{_alt.a, _alt.l ? std::make_unique<List<A>>() : nullptr};
        auto &_dst_alt = std::get<Cons>(_dst->v_);
        if (_alt.l) {
          _stack.push_back({_alt.l.get(), _dst_alt.l.get()});
        }
      }
    }
    return _out;
  }

  // CREATORS
  template <typename _U> explicit List(const List<_U> &_other) {
    if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
      this->v_ = Nil{};
    } else {
      const auto &[a, l] = std::get<typename List<_U>::Cons>(_other.v());
      this->v_ = Cons{A(a), l ? std::make_unique<List<A>>(*l) : nullptr};
    }
  }

  static List<A> nil() { return List(Nil{}); }

  static List<A> cons(A a, List<A> l) {
    return List(Cons{std::move(a), std::make_unique<List<A>>(std::move(l))});
  }

  // MANIPULATORS
  ~List() {
    std::vector<std::unique_ptr<List<A>>> _stack{};
    _stack.reserve(8);
    auto _drain = [&](List<A> &_node) {
      if (std::holds_alternative<Cons>(_node.v_)) {
        auto &_alt = std::get<Cons>(_node.v_);
        if (_alt.l) {
          _stack.push_back(std::move(_alt.l));
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

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, T1 &, A &>
  T1 fold_left(F0 &&f, T1 a0) const {
    if (std::holds_alternative<typename List<A>::Nil>(this->v())) {
      return a0;
    } else {
      const auto &[a1, a2] = std::get<typename List<A>::Cons>(this->v());
      return a2->template fold_left<T1>(f, f(a0, a1));
    }
  }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, A &>
  List<T1> map(F0 &&f) const {
    if (std::holds_alternative<typename List<A>::Nil>(this->v())) {
      return List<T1>::nil();
    } else {
      const auto &[a0, a1] = std::get<typename List<A>::Cons>(this->v());
      return List<T1>::cons(f(a0), a1->template map<T1>(f));
    }
  }
};

template <typename M>
concept HasRecord = requires {
  typename M::R;
  {
    M::mk(std::declval<uint64_t>(), std::declval<uint64_t>())
  } -> std::same_as<typename M::R>;
  { M::get_x(std::declval<typename M::R>()) } -> std::same_as<uint64_t>;
  { M::get_y(std::declval<typename M::R>()) } -> std::same_as<uint64_t>;
};

struct RecordFieldPatterns {
  struct Point {
    uint64_t px;
    uint64_t py;

    // ACCESSORS
    Point clone() const { return Point{this->px, this->py}; }
  };

  static uint64_t classify_point(const Point &p);
  static uint64_t zero_x(const Point &p);

  template <typename T1> static T1 identity(T1 x) { return x; }

  /// Apply a polymorphic function to a record — the record type flows
  /// through a type variable.
  static Point id_point(const Point &_x0);

  /// Polymorphic projection: the match happens inside a polymorphic context
  /// where the scrutinee's type might not be Tglob.
  template <typename T1, typename T2>
  static T1 generic_first(const std::pair<T1, T2> &_x0) {
    return _x0.first;
  }

  static std::pair<uint64_t, uint64_t> point_pair(const Point &p);
  static uint64_t first_coord(const Point &p);

  /// Record whose field default depends on the section variable.
  struct ScaledPoint {
    uint64_t sp_x;
    uint64_t sp_y;

    // ACCESSORS
    ScaledPoint clone() const { return ScaledPoint{this->sp_x, this->sp_y}; }
  };

  static uint64_t scaled_sum(uint64_t scale, const ScaledPoint &sp);
  /// After section closing, scaled_sum is parameterized by scale : nat.
  /// The record type itself is NOT parameterized (scale is only used in
  /// the function body), but the function signature changes.
  static inline const uint64_t test_labeled =
      scaled_sum(UINT64_C(3), ScaledPoint{UINT64_C(10), UINT64_C(20)});

  struct PointImpl {
    using R = Point;
    static Point mk(uint64_t x, uint64_t x0);
    static uint64_t get_x(const Point &p);
    static uint64_t get_y(const Point &p);
  };

  template <HasRecord M> struct UseRecord {
    static uint64_t sum_fields(typename M::R r) {
      return (M::get_x(r) + M::get_y(r));
    }
  };

  using UR = UseRecord<PointImpl>;
  static inline const uint64_t test_functor =
      UR::sum_fields(Point{UINT64_C(100), UINT64_C(200)});

  struct Segment {
    Point seg_start;
    Point seg_end;

    // ACCESSORS
    Segment clone() const {
      return Segment{this->seg_start.clone(), this->seg_end.clone()};
    }
  };

  static uint64_t segment_length_sq(const Segment &s);

  struct Bounded {
    uint64_t lo;
    uint64_t hi;
    uint64_t mid;

    // ACCESSORS
    Bounded clone() const { return Bounded{this->lo, this->hi, this->mid}; }
  };

  static uint64_t bounded_range(const Bounded &b);
  static uint64_t sum_px(const List<Point> &points);
  static List<uint64_t> map_py(const List<Point> &points);
  static Point swap(const Point &p);
  static Point double_swap(const Point &p);

  struct Container {
    std::any elem;
    uint64_t count;

    // ACCESSORS
    Container clone() const { return Container{this->elem, this->count}; }
  };

  using elem_type = std::any;
  static uint64_t get_count(const Container &c);
  static inline const uint64_t test_container =
      get_count(Container{UINT64_C(42), UINT64_C(5)});
  static inline const uint64_t test_origin =
      classify_point(Point{UINT64_C(0), UINT64_C(0)});
  static inline const uint64_t test_y_axis =
      classify_point(Point{UINT64_C(0), UINT64_C(5)});
  static inline const uint64_t test_x_axis =
      classify_point(Point{UINT64_C(3), UINT64_C(0)});
  static inline const uint64_t test_general =
      classify_point(Point{UINT64_C(3), UINT64_C(4)});
  static inline const uint64_t test_zero_x =
      zero_x(Point{UINT64_C(0), UINT64_C(42)});
  static inline const uint64_t test_nonzero =
      zero_x(Point{UINT64_C(5), UINT64_C(10)});
  static inline const Point test_id =
      id_point(Point{UINT64_C(99), UINT64_C(1)});
  static inline const uint64_t test_seg = segment_length_sq(Segment{
      Point{UINT64_C(1), UINT64_C(2)}, Point{UINT64_C(4), UINT64_C(6)}});
  static inline const uint64_t test_sum = sum_px(List<Point>::cons(
      Point{UINT64_C(10), UINT64_C(0)},
      List<Point>::cons(Point{UINT64_C(20), UINT64_C(0)},
                        List<Point>::cons(Point{UINT64_C(30), UINT64_C(0)},
                                          List<Point>::nil()))));
  static inline const List<uint64_t> test_map = map_py(List<Point>::cons(
      Point{UINT64_C(0), UINT64_C(1)},
      List<Point>::cons(Point{UINT64_C(0), UINT64_C(2)},
                        List<Point>::cons(Point{UINT64_C(0), UINT64_C(3)},
                                          List<Point>::nil()))));
  static inline const Point test_swap = swap(Point{UINT64_C(3), UINT64_C(7)});
};

#endif // INCLUDED_RECORD_FIELD_PATTERNS
