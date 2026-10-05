#ifndef INCLUDED_RECORD_FIELD_PATTERNS
#define INCLUDED_RECORD_FIELD_PATTERNS

#include "crane_fn.h"
#include "obj.h"
#include <atomic>
#include <concepts>
#include <cstdint>
#include <memory>
#include <optional>
#include <stdexcept>
#include <type_traits>
#include <utility>
#include <variant>

template <typename A> struct List;

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
      : v_(crane_convert_spine(
            _other, std::shared_ptr<List<A>>(nullptr),
            [](const List<CraneU> &_cell) -> const List<CraneU> * {
              if (std::holds_alternative<typename List<CraneU>::Cons>(
                      _cell.v())) {
                return std::get<typename List<CraneU>::Cons>(_cell.v()).l.get();
              } else {
                return nullptr;
              }
            },
            [&](const List<CraneU> &_other,
                std::shared_ptr<List<A>> _below) -> variant_t {
              if (std::holds_alternative<typename List<CraneU>::Nil>(
                      _other.v())) {
                return Nil{};
              } else {
                const auto &[a, l] =
                    std::get<typename List<CraneU>::Cons>(_other.v());
                return Cons{
                    [&]() -> A {
                      if constexpr (crane_convertible<A, const CraneU &>) {
                        return crane_convert<A>(a);
                      } else {
                        throw std::logic_error(
                            "unreachable: inactive constructor field at this "
                            "instantiation");
                      }
                    }(),
                    std::move(_below)};
              }
            },
            [](auto &&_alt) {
              return std::make_shared<List<A>>(std::move(_alt));
            })) {}

  static List<A> nil() { return List<A>(Nil{}); }

  static List<A> cons(A a, List<A> l) {
    return List<A>(Cons{std::move(a), std::make_shared<List<A>>(std::move(l))});
  }

  // MANIPULATORS
  ~List() {
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

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, T1 &&, const A &>
  T1 fold_left(F0 &&f, T1 a0) const {
    const List<A> *_loop_self = this;
    T1 _loop_a0 = std::move(a0);
    while (true) {
      auto &&_sv = *_loop_self;
      if (std::holds_alternative<typename List<A>::Nil>(_sv.v())) {
        return _loop_a0;
      } else {
        const auto &[a1, a2] = std::get<typename List<A>::Cons>(_sv.v());
        _loop_self = crane_raw(a2);
        _loop_a0 = f(std::move(_loop_a0), a1);
      }
    }
  }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, const A &>
  List<T1> map(F0 &&f) const {
    std::optional<List<T1>> _root{};
    std::shared_ptr<List<T1>> *_write = nullptr;
    const List<A> *_loop_self = this;
    while (true) {
      auto &&_sv = *_loop_self;
      if (std::holds_alternative<typename List<A>::Nil>(_sv.v())) {
        auto _value = List<T1>::nil();
        (_write ? *(*_write = std::make_shared<List<T1>>(std::move(_value)))
                : _root.emplace(std::move(_value)));
        break;
      } else {
        const auto &[a0, a1] = std::get<typename List<A>::Cons>(_sv.v());
        auto _cell = typename List<T1>::Cons(f(a0), nullptr);
        List<T1> &_node =
            (_write ? *(*_write = std::make_shared<List<T1>>(std::move(_cell)))
                    : _root.emplace(std::move(_cell)));
        _write = &std::get<typename List<T1>::Cons>(_node.v_mut()).l;
        _loop_self = crane_raw(a1);
        continue;
      }
    }
    return std::move(*_root);
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
  };

  static uint64_t classify_point(const Point &p);
  static uint64_t zero_x(const Point &p);

  template <typename T1> static T1 identity(T1 x) { return x; }

  /// Apply a polymorphic function to a record — the record type flows
  /// through a type variable.
  static Point id_point(const Point &x0_);

  /// Polymorphic projection: the match happens inside a polymorphic context
  /// where the scrutinee's type might not be Tglob.
  template <typename T1, typename T2>
  static T1 generic_first(const std::pair<T1, T2> &x0_) {
    return x0_.first;
  }

  static std::pair<uint64_t, uint64_t> point_pair(const Point &p);
  static uint64_t first_coord(const Point &p);

  /// Record whose field default depends on the section variable.
  struct ScaledPoint {
    uint64_t sp_x;
    uint64_t sp_y;
  };

  static uint64_t scaled_sum(uint64_t scale, const ScaledPoint &sp);
  /// After section closing, scaled_sum is parameterized by scale : nat.
  /// The record type itself is NOT parameterized (scale is only used in
  /// the function body), but the function signature changes.
  static constexpr uint64_t test_labeled = UINT64_C(90);

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
  };

  static uint64_t segment_length_sq(const Segment &s);

  struct Bounded {
    uint64_t lo;
    uint64_t hi;
    uint64_t mid;
  };

  static uint64_t bounded_range(const Bounded &b);
  static uint64_t sum_px(const List<Point> &points);
  static List<uint64_t> map_py(const List<Point> &points);
  static Point swap(const Point &p);
  static Point double_swap(const Point &p);

  struct Container {
    crane::obj elem;
    uint64_t count;
  };

  using elem_type = crane::obj;
  static uint64_t get_count(const Container &c);
  static constexpr uint64_t test_container = UINT64_C(5);
  static constexpr uint64_t test_origin = UINT64_C(0);
  static constexpr uint64_t test_y_axis = UINT64_C(1);
  static constexpr uint64_t test_x_axis = UINT64_C(2);
  static constexpr uint64_t test_general = UINT64_C(7);
  static constexpr uint64_t test_zero_x = UINT64_C(42);
  static constexpr uint64_t test_nonzero = UINT64_C(14);
  static inline const Point test_id =
      id_point(Point{UINT64_C(99), UINT64_C(1)});
  static constexpr uint64_t test_seg = UINT64_C(25);
  static constexpr uint64_t test_sum = UINT64_C(60);
  static inline const List<uint64_t> test_map = map_py(List<Point>::cons(
      Point{UINT64_C(0), UINT64_C(1)},
      List<Point>::cons(Point{UINT64_C(0), UINT64_C(2)},
                        List<Point>::cons(Point{UINT64_C(0), UINT64_C(3)},
                                          List<Point>::nil()))));
  static inline const Point test_swap = swap(Point{UINT64_C(3), UINT64_C(7)});
};

#endif // INCLUDED_RECORD_FIELD_PATTERNS
