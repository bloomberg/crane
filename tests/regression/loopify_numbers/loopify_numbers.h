#ifndef INCLUDED_LOOPIFY_NUMBERS
#define INCLUDED_LOOPIFY_NUMBERS

#include <memory>
#include <type_traits>
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

  unsigned int length() const {
    const List *_self = this;

    /// _Enter: captures varying parameters for each recursive call.
    struct _Enter {
      const List *_self;
    };

    /// _Resume_Cons: resumes after recursive call with _result.
    struct _Resume_Cons {};

    using _Frame = std::variant<_Enter, _Resume_Cons>;
    unsigned int _result{};
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
          _result = 0u;
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
  static unsigned int factorial(unsigned int n);
  static unsigned int fib(unsigned int n);
  static unsigned int tribonacci_fuel(unsigned int fuel, unsigned int n);
  static unsigned int tribonacci(unsigned int n);
  static unsigned int gcd_fuel(unsigned int fuel, unsigned int a,
                               unsigned int b);
  static unsigned int gcd(unsigned int a, unsigned int b);
  static unsigned int binomial(unsigned int n, unsigned int k);
  static unsigned int pascal(unsigned int row, unsigned int col);
  static unsigned int ackermann_fuel(unsigned int fuel, unsigned int m,
                                     unsigned int n);
  static unsigned int ack(unsigned int m, unsigned int n);
  static unsigned int collatz_length_fuel(unsigned int fuel, unsigned int n);
  static unsigned int collatz_length(unsigned int n);
  static unsigned int digitsum_fuel(unsigned int fuel, unsigned int n);
  static unsigned int digitsum(unsigned int n);
  static unsigned int dec_to_bin_fuel(unsigned int fuel, unsigned int n);
  static unsigned int dec_to_bin(unsigned int n);
  static unsigned int sum_to(unsigned int n);
  static unsigned int sum_squares(unsigned int n);
  static unsigned int alternating_sum(bool sign, unsigned int acc,
                                      unsigned int n);
  static unsigned int staircase_fuel(unsigned int fuel, unsigned int n);
  static unsigned int staircase(unsigned int n);

  /// church n f x applies function f to x exactly n times.
  /// Tests recursive higher-order function application.
  template <typename F1>
    requires std::is_invocable_r_v<unsigned int, F1 &, unsigned int &>
  static unsigned int church(unsigned int n, F1 &&f, unsigned int x) {
    unsigned int _result;
    unsigned int _loop_x = std::move(x);
    unsigned int _loop_n = std::move(n);
    while (true) {
      if (_loop_n <= 0) {
        _result = std::move(_loop_x);
        break;
      } else {
        unsigned int m = _loop_n - 1;
        _loop_x = f(_loop_x);
        _loop_n = m;
      }
    }
    return _result;
  }

  /// iterate_pred n applies predecessor n times, starting from n.
  /// Tests church-style iteration with concrete function.
  static unsigned int iterate_pred(unsigned int n);

  /// nest_apply n f x nests function application: f(f(...f(x))).
  /// Similar to church but emphasizes nested call structure.
  template <typename F1>
    requires std::is_invocable_r_v<unsigned int, F1 &, unsigned int &>
  static unsigned int
  nest_apply(unsigned int n, F1 &&f,
             unsigned int x) { /// _Enter: captures varying parameters for each
                               /// recursive call.

    struct _Enter {
      unsigned int n;
    };

    /// _Resume__x: saves [f], resumes after recursive call with _result.
    struct _Resume__x {
      F1 f;
    };

    using _Frame = std::variant<_Enter, _Resume__x>;
    unsigned int _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{n});
    /// Loopified nest_apply: _Enter -> _Resume__x.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        unsigned int n = _f.n;
        if (n <= 0) {
          _result = std::move(x);
        } else {
          unsigned int n_ = n - 1;
          if (n_ <= 0) {
            _result = f(x);
          } else {
            unsigned int _x = n_ - 1;
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
  static unsigned int sum_while_positive(unsigned int n);
  /// count_down_by k n counts down from n by steps of k.
  /// Tests recursion with non-standard step size.
  static unsigned int count_down_by_fuel(unsigned int fuel, unsigned int k,
                                         unsigned int n);
  static unsigned int count_down_by(unsigned int k, unsigned int n);
  /// mixed_arith n combines multiplication and addition in recursion.
  static unsigned int mixed_arith_fuel(unsigned int fuel, unsigned int n);
  static unsigned int mixed_arith(unsigned int n);
  /// is_even n checks if n is even (mutually recursive with is_odd).
  static bool is_even_fuel(unsigned int fuel, unsigned int n);
  static bool is_odd_fuel(unsigned int fuel, unsigned int n);
  static bool is_even(unsigned int n);
  static bool is_odd(unsigned int n);
  /// power b e computes b^e.
  static unsigned int power(unsigned int b, unsigned int e);
  /// power_mod b e m computes (b^e) mod m efficiently.
  static unsigned int power_mod_fuel(unsigned int fuel, unsigned int b,
                                     unsigned int e, unsigned int m);
  static unsigned int power_mod(unsigned int b, unsigned int e, unsigned int m);
  /// sum_divisors n sums all divisors of n (excluding n itself).
  static unsigned int sum_divisors_aux(unsigned int n, unsigned int k);
  static unsigned int sum_divisors(unsigned int n);
  /// sum_odd_indices l and sum_even_indices l are mutually recursive.
  /// sum_odd_indices adds elements at odd positions (0, 2, 4...).
  /// sum_even_indices processes even positions (1, 3, 5...) by calling
  /// sum_odd_indices.
  static unsigned int sum_odd_indices_fuel(unsigned int fuel,
                                           const List<unsigned int> &l);
  static unsigned int sum_even_indices_fuel(unsigned int fuel,
                                            const List<unsigned int> &l);
  static unsigned int sum_odd_indices(const List<unsigned int> &l);
  static unsigned int sum_even_indices(const List<unsigned int> &l);
  /// collatz_list n generates collatz sequence as a list.
  static List<unsigned int> collatz_list_fuel(unsigned int fuel,
                                              unsigned int n);
  static List<unsigned int> collatz_list(unsigned int n);
  /// sum_divisible_by k n sums all numbers from 1 to n divisible by k.
  static unsigned int sum_divisible_by(unsigned int k, unsigned int n);
};

#endif // INCLUDED_LOOPIFY_NUMBERS
