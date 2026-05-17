#ifndef INCLUDED_NUMERAL_STRESS
#define INCLUDED_NUMERAL_STRESS

#include <cstdint>
#include <memory>
#include <optional>
#include <utility>
#include <variant>
#include <vector>

template <typename A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    A a0;
    std::unique_ptr<List<A>> a1;
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
        _dst->v_ =
            Cons{_alt.a0, _alt.a1 ? std::make_unique<List<A>>() : nullptr};
        auto &_dst_alt = std::get<Cons>(_dst->v_);
        if (_alt.a1) {
          _stack.push_back({_alt.a1.get(), _dst_alt.a1.get()});
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
      const auto &[a0, a1] = std::get<typename List<_U>::Cons>(_other.v());
      this->v_ = Cons{A(a0), a1 ? std::make_unique<List<A>>(*a1) : nullptr};
    }
  }

  static List<A> nil() { return List(Nil{}); }

  static List<A> cons(A a0, List<A> a1) {
    return List(Cons{std::move(a0), std::make_unique<List<A>>(std::move(a1))});
  }

  // MANIPULATORS
  ~List() {
    std::vector<std::unique_ptr<List<A>>> _stack{};
    _stack.reserve(8);
    auto _drain = [&](List<A> &_node) {
      if (std::holds_alternative<Cons>(_node.v_)) {
        auto &_alt = std::get<Cons>(_node.v_);
        if (_alt.a1) {
          _stack.push_back(std::move(_alt.a1));
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
};

struct NumeralStress {
  /// 1. Numeral inside option
  static inline const std::optional<uint64_t> opt_100 =
      std::make_optional<uint64_t>(UINT64_C(100));
  static inline const std::optional<int64_t> opt_neg =
      std::make_optional<int64_t>(INT64_C(-50)); /// 2. Numeral in a pair
  static inline const std::pair<uint64_t, int64_t> pair_nums =
      std::make_pair(UINT64_C(42), INT64_C(-7));
  /// 3. Numeral in a list
  static inline const List<int64_t> z_list = List<int64_t>::cons(
      INT64_C(1),
      List<int64_t>::cons(
          INT64_C(-2), List<int64_t>::cons(INT64_C(3), List<int64_t>::nil())));
  /// 4. Numeral as argument to Nat.add
  static inline const uint64_t add_big = (UINT64_C(1000) + UINT64_C(2000));
  /// 5. Numeral in match scrutinee
  static inline const uint64_t match_numeral = UINT64_C(1);
  /// 6. Numeral inside a fixpoint
  static uint64_t count_from(uint64_t n, uint64_t target);
  static inline const uint64_t test_count =
      count_from(UINT64_C(100), UINT64_C(50));
  /// 7. Z arithmetic with literals
  static inline const int64_t z_complex =
      ((INT64_C(100) * INT64_C(200)) + (INT64_C(50) - INT64_C(25)));

  /// 8. Multiple numerals in one record
  struct point {
    uint64_t px;
    uint64_t py;

    // ACCESSORS
    point clone() const { return point{(*this).px, (*this).py}; }
  };

  static inline const point origin = point{UINT64_C(0), UINT64_C(0)};
  static inline const point far_point = point{UINT64_C(999), UINT64_C(888)};
  /// 9. Numeral in boolean expression
  static bool check_range(uint64_t n);
  static inline const bool test_range = check_range(UINT64_C(50));
  /// 10. Mixed nat and Z in one function
  static int64_t mixed_arith(uint64_t n);
  static inline const int64_t test_mixed = mixed_arith(UINT64_C(42));
};

#endif // INCLUDED_NUMERAL_STRESS
