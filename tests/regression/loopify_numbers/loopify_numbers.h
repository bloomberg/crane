#ifndef INCLUDED_LOOPIFY_NUMBERS
#define INCLUDED_LOOPIFY_NUMBERS

#include <any>
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
    const List *_self = this;

    /// _Enter: captures varying parameters for each recursive call.
    struct _Enter {
      const List *_self;
    };

    /// _Resume_Cons: resumes after recursive call with _result.
    struct _Resume_Cons {};

    using _Frame = std::variant<_Enter, _Resume_Cons>;
    uint64_t _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{_self});
    /// Loopified length: _Enter -> _Resume_Cons.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const List *_self = _f._self;
        auto &&_sv = *_self;
        if (std::holds_alternative<typename List<A>::Nil>(_sv.v())) {
          _result = UINT64_C(0);
        } else {
          const auto &[a0, a1] = std::get<typename List<A>::Cons>(_sv.v());
          _stack.emplace_back(_Resume_Cons{});
          _stack.emplace_back(_Enter{a1.get()});
        }
      } else {
        auto _f = std::move(std::get<_Resume_Cons>(_frame));
        _result = (_result + 1);
      }
    }
    return _result;
  }
};

/// Consolidated UNIQUE numeric algorithms - no basic arithmetic.
/// Tests loopification on number theory and recursive sequences.
struct LoopifyNumbers {
  static uint64_t factorial(uint64_t n);
  static uint64_t fib(uint64_t n);
  static uint64_t tribonacci_fuel(uint64_t fuel, uint64_t n);
  static uint64_t tribonacci(uint64_t n);
  static uint64_t gcd_fuel(uint64_t fuel, uint64_t a, uint64_t b);
  static uint64_t gcd(uint64_t a, uint64_t b);
  static uint64_t binomial(uint64_t n, uint64_t k);
  static uint64_t pascal(uint64_t row, uint64_t col);
  static uint64_t ackermann_fuel(uint64_t fuel, uint64_t m, uint64_t n);
  static uint64_t ack(uint64_t m, uint64_t n);
  static uint64_t collatz_length_fuel(uint64_t fuel, uint64_t n);
  static uint64_t collatz_length(uint64_t n);
  static uint64_t digitsum_fuel(uint64_t fuel, uint64_t n);
  static uint64_t digitsum(uint64_t n);
  static uint64_t dec_to_bin_fuel(uint64_t fuel, uint64_t n);
  static uint64_t dec_to_bin(uint64_t n);
  static uint64_t sum_to(uint64_t n);
  static uint64_t sum_squares(uint64_t n);
  static uint64_t alternating_sum(bool sign, uint64_t acc, uint64_t n);
  static uint64_t staircase_fuel(uint64_t fuel, uint64_t n);
  static uint64_t staircase(uint64_t n);

  /// church n f x applies function f to x exactly n times.
  /// Tests recursive higher-order function application.
  template <typename F1>
    requires std::is_invocable_r_v<uint64_t, F1 &, uint64_t &>
  static uint64_t church(uint64_t n, F1 &&f, uint64_t x) {
    uint64_t _loop_x = std::move(x);
    uint64_t _loop_n = std::move(n);
    while (true) {
      if (_loop_n <= 0) {
        return _loop_x;
      } else {
        uint64_t m = _loop_n - 1;
        _loop_x = f(_loop_x);
        _loop_n = m;
      }
    }
  }

  /// iterate_pred n applies predecessor n times, starting from n.
  /// Tests church-style iteration with concrete function.
  static uint64_t iterate_pred(uint64_t n);

  /// nest_apply n f x nests function application: f(f(...f(x))).
  /// Similar to church but emphasizes nested call structure.
  template <typename F1>
    requires std::is_invocable_r_v<uint64_t, F1 &, uint64_t &>
  static uint64_t
  nest_apply(uint64_t n, F1 &&f,
             uint64_t x) { /// _Enter: captures varying parameters for each
                           /// recursive call.

    struct _Enter {
      uint64_t n;
    };

    /// _Resume__x: saves [f], resumes after recursive call with _result.
    struct _Resume__x {
      F1 f;
    };

    using _Frame = std::variant<_Enter, _Resume__x>;
    uint64_t _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{n});
    /// Loopified nest_apply: _Enter -> _Resume__x.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        uint64_t n = _f.n;
        if (n <= 0) {
          _result = std::move(x);
        } else {
          uint64_t n_ = n - 1;
          if (n_ <= 0) {
            _result = f(x);
          } else {
            uint64_t _x = n_ - 1;
            _stack.emplace_back(_Resume__x{f});
            _stack.emplace_back(_Enter{n_});
          }
        }
      } else {
        auto _f = std::move(std::get<_Resume__x>(_frame));
        _result = _f.f(_result);
      }
    }
    return _result;
  }

  /// sum_while_positive n sums numbers from n down to 0, but only positive
  /// ones. Tests conditional accumulation in recursion.
  static uint64_t sum_while_positive(uint64_t n);
  /// count_down_by k n counts down from n by steps of k.
  /// Tests recursion with non-standard step size.
  static uint64_t count_down_by_fuel(uint64_t fuel, uint64_t k, uint64_t n);
  static uint64_t count_down_by(uint64_t k, uint64_t n);
  /// mixed_arith n combines multiplication and addition in recursion.
  static uint64_t mixed_arith_fuel(uint64_t fuel, uint64_t n);
  static uint64_t mixed_arith(uint64_t n);
  /// is_even n checks if n is even (mutually recursive with is_odd).
  static bool is_even_fuel(uint64_t fuel, uint64_t n);
  static bool is_odd_fuel(uint64_t fuel, uint64_t n);
  static bool is_even(uint64_t n);
  static bool is_odd(uint64_t n);
  /// power b e computes b^e.
  static uint64_t power(uint64_t b, uint64_t e);
  /// power_mod b e m computes (b^e) mod m efficiently.
  static uint64_t power_mod_fuel(uint64_t fuel, uint64_t b, uint64_t e,
                                 uint64_t m);
  static uint64_t power_mod(uint64_t b, uint64_t e, uint64_t m);
  /// sum_divisors n sums all divisors of n (excluding n itself).
  static uint64_t sum_divisors_aux(uint64_t n, uint64_t k);
  static uint64_t sum_divisors(uint64_t n);
  /// sum_odd_indices l and sum_even_indices l are mutually recursive.
  /// sum_odd_indices adds elements at odd positions (0, 2, 4...).
  /// sum_even_indices processes even positions (1, 3, 5...) by calling
  /// sum_odd_indices.
  static uint64_t sum_odd_indices_fuel(uint64_t fuel, const List<uint64_t> &l);
  static uint64_t sum_even_indices_fuel(uint64_t fuel, const List<uint64_t> &l);
  static uint64_t sum_odd_indices(const List<uint64_t> &l);
  static uint64_t sum_even_indices(const List<uint64_t> &l);
  /// collatz_list n generates collatz sequence as a list.
  static List<uint64_t> collatz_list_fuel(uint64_t fuel, uint64_t n);
  static List<uint64_t> collatz_list(uint64_t n);
  /// sum_divisible_by k n sums all numbers from 1 to n divisible by k.
  static uint64_t sum_divisible_by(uint64_t k, uint64_t n);
};

#endif // INCLUDED_LOOPIFY_NUMBERS
