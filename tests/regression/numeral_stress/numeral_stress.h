#ifndef INCLUDED_NUMERAL_STRESS
#define INCLUDED_NUMERAL_STRESS

#include <cstdint>
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
  List clone() const {
    List _out{};

    struct _CloneFrame {
      const List *_src;
      List *_dst;
    };

    std::vector<_CloneFrame> _stack;
    _stack.push_back({this, &_out});
    while (!_stack.empty()) {
      auto _frame = _stack.back();
      _stack.pop_back();
      const List *_src = _frame._src;
      List *_dst = _frame._dst;
      if (std::holds_alternative<Nil>(_src->v())) {
        const auto &_alt = std::get<Nil>(_src->v());
        _dst->d_v_ = Nil{};
      } else {
        const auto &_alt = std::get<Cons>(_src->v());
        _dst->d_v_ =
            Cons{_alt.d_a0, _alt.d_a1 ? std::make_unique<List>() : nullptr};
        auto &_dst_alt = std::get<Cons>(_dst->d_v_);
        if (_alt.d_a1)
          _stack.push_back({_alt.d_a1.get(), _dst_alt.d_a1.get()});
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
    std::vector<std::unique_ptr<List>> _stack;
    auto _drain = [&](List &_node) {
      if (std::holds_alternative<Cons>(_node.d_v_)) {
        auto &_alt = std::get<Cons>(_node.d_v_);
        if (_alt.d_a1)
          _stack.push_back(std::move(_alt.d_a1));
      }
    };
    _drain(*this);
    while (!_stack.empty()) {
      auto _node = std::move(_stack.back());
      _stack.pop_back();
      if (_node)
        _drain(*_node);
    }
  }

  inline variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  const variant_t &v() const { return d_v_; }
};

struct NumeralStress {
  /// 1. Numeral inside option
  static inline const std::optional<unsigned int> opt_100 =
      std::make_optional<unsigned int>(100u);
  static inline const std::optional<int64_t> opt_neg =
      std::make_optional<int64_t>(INT64_C(-50)); /// 2. Numeral in a pair
  static inline const std::pair<unsigned int, int64_t> pair_nums =
      std::make_pair(42u, INT64_C(-7));
  /// 3. Numeral in a list
  static inline const List<int64_t> z_list = List<int64_t>::cons(
      INT64_C(1),
      List<int64_t>::cons(
          INT64_C(-2), List<int64_t>::cons(INT64_C(3), List<int64_t>::nil())));
  /// 4. Numeral as argument to Nat.add
  static inline const unsigned int add_big = (1000u + 2000u);
  /// 5. Numeral in match scrutinee
  static inline const unsigned int match_numeral = 1u;
  /// 6. Numeral inside a fixpoint
  static unsigned int count_from(unsigned int n, const unsigned int &target);
  static inline const unsigned int test_count = count_from(100u, 50u);
  /// 7. Z arithmetic with literals
  static inline const int64_t z_complex =
      ((INT64_C(100) * INT64_C(200)) + (INT64_C(50) - INT64_C(25)));

  /// 8. Multiple numerals in one record
  struct point {
    unsigned int px;
    unsigned int py;

    // ACCESSORS
    point clone() const { return point{(*(this)).px, (*(this)).py}; }
  };

  static inline const point origin = point{0u, 0u};
  static inline const point far_point = point{999u, 888u};
  /// 9. Numeral in boolean expression
  static bool check_range(const unsigned int &n);
  static inline const bool test_range = check_range(50u);
  /// 10. Mixed nat and Z in one function
  static int64_t mixed_arith(const unsigned int &n);
  static inline const int64_t test_mixed = mixed_arith(42u);
};

#endif // INCLUDED_NUMERAL_STRESS
