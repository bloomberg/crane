#ifndef INCLUDED_LOOPIFY_NUMBERS
#define INCLUDED_LOOPIFY_NUMBERS

#include <memory>
#include <type_traits>
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

  __attribute__((pure)) unsigned int length() const {
    const List *_self = this;

    struct _Enter {
      const List *_self;
    };

    struct _Call1 {};

    using _Frame = std::variant<_Enter, _Call1>;
    unsigned int _result{};
    std::vector<_Frame> _stack;
    _stack.push_back(_Enter{_self});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      std::visit(
          Overloaded{
              [&](_Enter _f) {
                const List *_self = _f._self;
                std::visit(
                    Overloaded{
                        [&](const typename List<t_A>::Nil _args) -> void {
                          _result = 0u;
                        },
                        [&](const typename List<t_A>::Cons _args) -> void {
                          _stack.push_back(_Call1{});
                          _stack.push_back(_Enter{_args.d_a1.get()});
                        }},
                    _self->v());
              },
              [&](_Call1 _f) { _result = (_result + 1); }},
          _frame);
    }
    return _result;
  }
};

struct Nat {
  __attribute__((pure)) static std::pair<unsigned int, unsigned int>
  divmod(const unsigned int x, const unsigned int y, const unsigned int q,
         const unsigned int u);
  __attribute__((pure)) static unsigned int div(const unsigned int x,
                                                const unsigned int y);
};

/// Consolidated UNIQUE numeric algorithms - no basic arithmetic.
/// Tests loopification on number theory and recursive sequences.
struct LoopifyNumbers {
  __attribute__((pure)) static unsigned int factorial(const unsigned int n);
  __attribute__((pure)) static unsigned int fib(const unsigned int n);
  __attribute__((pure)) static unsigned int
  tribonacci_fuel(const unsigned int fuel, const unsigned int n);
  __attribute__((pure)) static unsigned int tribonacci(const unsigned int n);
  __attribute__((pure)) static unsigned int
  gcd_fuel(const unsigned int fuel, const unsigned int a, const unsigned int b);
  __attribute__((pure)) static unsigned int gcd(const unsigned int a,
                                                const unsigned int b);
  __attribute__((pure)) static unsigned int binomial(const unsigned int n,
                                                     const unsigned int k);
  __attribute__((pure)) static unsigned int pascal(const unsigned int row,
                                                   const unsigned int col);
  __attribute__((pure)) static unsigned int
  ackermann_fuel(const unsigned int fuel, const unsigned int m,
                 const unsigned int n);
  __attribute__((pure)) static unsigned int ack(const unsigned int m,
                                                const unsigned int n);
  __attribute__((pure)) static unsigned int
  collatz_length_fuel(const unsigned int fuel, const unsigned int n);
  __attribute__((pure)) static unsigned int
  collatz_length(const unsigned int n);
  __attribute__((pure)) static unsigned int
  digitsum_fuel(const unsigned int fuel, const unsigned int n);
  __attribute__((pure)) static unsigned int digitsum(const unsigned int n);
  __attribute__((pure)) static unsigned int
  dec_to_bin_fuel(const unsigned int fuel, const unsigned int n);
  __attribute__((pure)) static unsigned int dec_to_bin(const unsigned int n);
  __attribute__((pure)) static unsigned int sum_to(const unsigned int n);
  __attribute__((pure)) static unsigned int sum_squares(const unsigned int n);
  __attribute__((pure)) static unsigned int
  alternating_sum(const bool sign, const unsigned int acc,
                  const unsigned int n);
  __attribute__((pure)) static unsigned int
  staircase_fuel(const unsigned int fuel, const unsigned int n);
  __attribute__((pure)) static unsigned int
  staircase(const unsigned int
                n); /// church n f x applies function f to x exactly n times.

  /// Tests recursive higher-order function application.
  template <MapsTo<unsigned int, unsigned int> F1>
  __attribute__((pure)) static unsigned int church(const unsigned int n, F1 &&f,
                                                   const unsigned int x) {
    unsigned int _result;
    unsigned int _loop_x = x;
    unsigned int _loop_n = n;
    bool _continue = true;
    while (_continue) {
      if (_loop_n <= 0) {
        {
          _result = std::move(_loop_x);
          _continue = false;
        }
      } else {
        unsigned int m = _loop_n - 1;
        {
          unsigned int _next_x = f(_loop_x);
          unsigned int _next_n = std::move(m);
          _loop_x = std::move(_next_x);
          _loop_n = std::move(_next_n);
          continue;
        }
      }
    }
    return _result;
  }

  /// iterate_pred n applies predecessor n times, starting from n.
  /// Tests church-style iteration with concrete function.
  __attribute__((pure)) static unsigned int iterate_pred(const unsigned int n);

  /// nest_apply n f x nests function application: f(f(...f(x))).
  /// Similar to church but emphasizes nested call structure.
  template <MapsTo<unsigned int, unsigned int> F1>
  __attribute__((pure)) static unsigned int
  nest_apply(const unsigned int n, F1 &&f, const unsigned int x) {
    struct _Enter {
      const unsigned int n;
    };

    struct _Call1 {};

    using _Frame = std::variant<_Enter, _Call1>;
    unsigned int _result{};
    std::vector<_Frame> _stack;
    _stack.push_back(_Enter{n});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      std::visit(Overloaded{[&](_Enter _f) {
                              const unsigned int n = _f.n;
                              if (n <= 0) {
                                _result = std::move(x);
                              } else {
                                unsigned int n_ = n - 1;
                                if (n_ <= 0) {
                                  _result = f(x);
                                } else {
                                  unsigned int _x = n_ - 1;
                                  _stack.push_back(_Call1{});
                                  _stack.push_back(_Enter{n_});
                                }
                              }
                            },
                            [&](_Call1 _f) { _result = f(_result); }},
                 _frame);
    }
    return _result;
  }

  /// sum_while_positive n sums numbers from n down to 0, but only positive
  /// ones. Tests conditional accumulation in recursion.
  __attribute__((pure)) static unsigned int
  sum_while_positive(const unsigned int n);
  /// count_down_by k n counts down from n by steps of k.
  /// Tests recursion with non-standard step size.
  __attribute__((pure)) static unsigned int
  count_down_by_fuel(const unsigned int fuel, const unsigned int k,
                     const unsigned int n);
  __attribute__((pure)) static unsigned int count_down_by(const unsigned int k,
                                                          const unsigned int n);
  /// mixed_arith n combines multiplication and addition in recursion.
  __attribute__((pure)) static unsigned int
  mixed_arith_fuel(const unsigned int fuel, const unsigned int n);
  __attribute__((pure)) static unsigned int mixed_arith(const unsigned int n);
  /// is_even n checks if n is even (mutually recursive with is_odd).
  __attribute__((pure)) static bool is_even_fuel(const unsigned int fuel,
                                                 const unsigned int n);
  __attribute__((pure)) static bool is_odd_fuel(const unsigned int fuel,
                                                const unsigned int n);
  __attribute__((pure)) static bool is_even(const unsigned int n);
  __attribute__((pure)) static bool is_odd(const unsigned int n);
  /// power b e computes b^e.
  __attribute__((pure)) static unsigned int power(const unsigned int b,
                                                  const unsigned int e);
  /// power_mod b e m computes (b^e) mod m efficiently.
  __attribute__((pure)) static unsigned int
  power_mod_fuel(const unsigned int fuel, const unsigned int b,
                 const unsigned int e, const unsigned int m);
  __attribute__((pure)) static unsigned int
  power_mod(const unsigned int b, const unsigned int e, const unsigned int m);
  /// sum_divisors n sums all divisors of n (excluding n itself).
  __attribute__((pure)) static unsigned int
  sum_divisors_aux(const unsigned int n, const unsigned int k);
  __attribute__((pure)) static unsigned int sum_divisors(const unsigned int n);
  /// sum_odd_indices l and sum_even_indices l are mutually recursive.
  /// sum_odd_indices adds elements at odd positions (0, 2, 4...).
  /// sum_even_indices processes even positions (1, 3, 5...) by calling
  /// sum_odd_indices.
  __attribute__((pure)) static unsigned int
  sum_odd_indices_fuel(const unsigned int fuel,
                       const std::shared_ptr<List<unsigned int>> &l);
  __attribute__((pure)) static unsigned int
  sum_even_indices_fuel(const unsigned int fuel,
                        const std::shared_ptr<List<unsigned int>> &l);
  __attribute__((pure)) static unsigned int
  sum_odd_indices(const std::shared_ptr<List<unsigned int>> &l);
  __attribute__((pure)) static unsigned int sum_even_indices(
      const std::shared_ptr<List<unsigned int>>
          &l); /// collatz_list n generates collatz sequence as a list.
  static std::shared_ptr<List<unsigned int>>
  collatz_list_fuel(const unsigned int fuel, const unsigned int n);
  static std::shared_ptr<List<unsigned int>> collatz_list(const unsigned int n);
  /// sum_divisible_by k n sums all numbers from 1 to n divisible by k.
  __attribute__((pure)) static unsigned int
  sum_divisible_by(const unsigned int k, const unsigned int n);
};

#endif // INCLUDED_LOOPIFY_NUMBERS
