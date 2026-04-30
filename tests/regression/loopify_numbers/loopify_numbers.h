#ifndef INCLUDED_LOOPIFY_NUMBERS
#define INCLUDED_LOOPIFY_NUMBERS

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

  unsigned int length() const {
    const List *_self = this;

    struct _Enter {
      const List *_self;
    };

    struct _Call1 {};

    using _Frame = std::variant<_Enter, _Call1>;
    unsigned int _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(16);
    _stack.emplace_back(_Enter{_self});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const List *_self = _f._self;
        auto &&_sv = *(_self);
        if (std::holds_alternative<typename List<t_A>::Nil>(_sv.v())) {
          _result = 0u;
        } else {
          const auto &[d_a0, d_a1] =
              std::get<typename List<t_A>::Cons>(_sv.v());
          _stack.emplace_back(_Call1{});
          _stack.emplace_back(_Enter{d_a1.get()});
        }
      } else {
        auto _f = std::move(std::get<_Call1>(_frame));
        _result = (_result + 1);
      }
    }
    return _result;
  }
};

/// Consolidated UNIQUE numeric algorithms - no basic arithmetic.
/// Tests loopification on number theory and recursive sequences.
struct LoopifyNumbers {
  static unsigned int factorial(const unsigned int &n);
  static unsigned int fib(const unsigned int &n);
  static unsigned int tribonacci_fuel(const unsigned int &fuel,
                                      const unsigned int &n);
  static unsigned int tribonacci(const unsigned int &n);
  static unsigned int gcd_fuel(const unsigned int &fuel, unsigned int a,
                               const unsigned int &b);
  static unsigned int gcd(const unsigned int &a, const unsigned int &b);
  static unsigned int binomial(const unsigned int &n, const unsigned int &k);
  static unsigned int pascal(const unsigned int &row, const unsigned int &col);
  static unsigned int ackermann_fuel(const unsigned int &fuel,
                                     const unsigned int &m, unsigned int n);
  static unsigned int ack(const unsigned int &m, const unsigned int &n);
  static unsigned int collatz_length_fuel(const unsigned int &fuel,
                                          const unsigned int &n);
  static unsigned int collatz_length(const unsigned int &n);
  static unsigned int digitsum_fuel(const unsigned int &fuel,
                                    const unsigned int &n);
  static unsigned int digitsum(const unsigned int &n);
  static unsigned int dec_to_bin_fuel(const unsigned int &fuel,
                                      const unsigned int &n);
  static unsigned int dec_to_bin(const unsigned int &n);
  static unsigned int sum_to(const unsigned int &n);
  static unsigned int sum_squares(const unsigned int &n);
  static unsigned int alternating_sum(const bool &sign, unsigned int acc,
                                      const unsigned int &n);
  static unsigned int staircase_fuel(const unsigned int &fuel,
                                     const unsigned int &n);
  static unsigned int staircase(const unsigned int &n);

  /// church n f x applies function f to x exactly n times.
  /// Tests recursive higher-order function application.
  template <MapsTo<unsigned int, unsigned int> F1>
  static unsigned int church(const unsigned int &n, F1 &&f, unsigned int x) {
    unsigned int _result;
    unsigned int _loop_x = std::move(x);
    unsigned int _loop_n = n;
    while (true) {
      if (_loop_n <= 0) {
        _result = _loop_x;
        break;
      } else {
        unsigned int m = _loop_n - 1;
        unsigned int _next_x = f(_loop_x);
        unsigned int _next_n = m;
        _loop_x = std::move(_next_x);
        _loop_n = std::move(_next_n);
      }
    }
    return _result;
  }

  /// iterate_pred n applies predecessor n times, starting from n.
  /// Tests church-style iteration with concrete function.
  static unsigned int iterate_pred(const unsigned int &n);

  /// nest_apply n f x nests function application: f(f(...f(x))).
  /// Similar to church but emphasizes nested call structure.
  template <MapsTo<unsigned int, unsigned int> F1>
  static unsigned int nest_apply(const unsigned int &n, F1 &&f,
                                 unsigned int x) {
    struct _Enter {
      unsigned int n;
    };

    struct _Call1 {};

    using _Frame = std::variant<_Enter, _Call1>;
    unsigned int _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(16);
    _stack.emplace_back(_Enter{n});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const unsigned int &n = _f.n;
        if (n <= 0) {
          _result = x;
        } else {
          unsigned int n_ = n - 1;
          if (n_ <= 0) {
            _result = f(x);
          } else {
            unsigned int _x = n_ - 1;
            _stack.emplace_back(_Call1{});
            _stack.emplace_back(_Enter{n_});
          }
        }
      } else {
        auto _f = std::move(std::get<_Call1>(_frame));
        _result = f(_result);
      }
    }
    return _result;
  }

  /// sum_while_positive n sums numbers from n down to 0, but only positive
  /// ones. Tests conditional accumulation in recursion.
  static unsigned int sum_while_positive(const unsigned int &n);
  /// count_down_by k n counts down from n by steps of k.
  /// Tests recursion with non-standard step size.
  static unsigned int count_down_by_fuel(const unsigned int &fuel,
                                         const unsigned int &k,
                                         const unsigned int &n);
  static unsigned int count_down_by(const unsigned int &k,
                                    const unsigned int &n);
  /// mixed_arith n combines multiplication and addition in recursion.
  static unsigned int mixed_arith_fuel(const unsigned int &fuel,
                                       const unsigned int &n);
  static unsigned int mixed_arith(const unsigned int &n);
  /// is_even n checks if n is even (mutually recursive with is_odd).
  static bool is_even_fuel(const unsigned int &fuel, const unsigned int &n);
  static bool is_odd_fuel(const unsigned int &fuel, const unsigned int &n);
  static bool is_even(const unsigned int &n);
  static bool is_odd(const unsigned int &n);
  /// power b e computes b^e.
  static unsigned int power(const unsigned int &b, const unsigned int &e);
  /// power_mod b e m computes (b^e) mod m efficiently.
  static unsigned int power_mod_fuel(const unsigned int &fuel,
                                     const unsigned int &b,
                                     const unsigned int &e,
                                     const unsigned int &m);
  static unsigned int power_mod(const unsigned int &b, const unsigned int &e,
                                const unsigned int &m);
  /// sum_divisors n sums all divisors of n (excluding n itself).
  static unsigned int sum_divisors_aux(const unsigned int &n,
                                       const unsigned int &k);
  static unsigned int sum_divisors(const unsigned int &n);
  /// sum_odd_indices l and sum_even_indices l are mutually recursive.
  /// sum_odd_indices adds elements at odd positions (0, 2, 4...).
  /// sum_even_indices processes even positions (1, 3, 5...) by calling
  /// sum_odd_indices.
  static unsigned int sum_odd_indices_fuel(const unsigned int &fuel,
                                           const List<unsigned int> &l);
  static unsigned int sum_even_indices_fuel(const unsigned int &fuel,
                                            const List<unsigned int> &l);
  static unsigned int sum_odd_indices(const List<unsigned int> &l);
  static unsigned int sum_even_indices(const List<unsigned int> &l);
  /// collatz_list n generates collatz sequence as a list.
  static List<unsigned int> collatz_list_fuel(const unsigned int &fuel,
                                              unsigned int n);
  static List<unsigned int> collatz_list(const unsigned int &n);
  /// sum_divisible_by k n sums all numbers from 1 to n divisible by k.
  static unsigned int sum_divisible_by(const unsigned int &k,
                                       const unsigned int &n);
};

#endif // INCLUDED_LOOPIFY_NUMBERS
