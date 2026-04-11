#ifndef INCLUDED_LOOPIFY_ALGORITHMS
#define INCLUDED_LOOPIFY_ALGORITHMS

#include <functional>
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

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }

  std::shared_ptr<List<t_A>> app(std::shared_ptr<List<t_A>> m) const {
    std::shared_ptr<List<t_A>> _head{};
    std::shared_ptr<List<t_A>> _last{};
    const List *_loop_self = this;
    bool _continue = true;
    while (_continue) {
      std::visit(
          Overloaded{
              [&](const typename List<t_A>::Nil) {
                if (_last) {
                  std::get<typename List<t_A>::Cons>(_last->v_mut()).d_a1 = m;
                } else {
                  _head = m;
                }
                _continue = false;
              },
              [&](const typename List<t_A>::Cons _args) {
                auto _cell = List<t_A>::cons(_args.d_a0, nullptr);
                if (_last) {
                  std::get<typename List<t_A>::Cons>(_last->v_mut()).d_a1 =
                      _cell;
                } else {
                  _head = _cell;
                }
                _last = _cell;
                _loop_self = _args.d_a1.get();
              }},
          _loop_self->v());
    }
    return _head;
  }
};

/// Consolidated UNIQUE list/sequence algorithms.
struct LoopifyAlgorithms {
  __attribute__((pure)) static unsigned int
  len_impl(const std::shared_ptr<List<unsigned int>> &l);
  /// sieve l Sieve of Eratosthenes - filters out multiples.
  static std::shared_ptr<List<unsigned int>>
  sieve_fuel(const unsigned int fuel, std::shared_ptr<List<unsigned int>> l);
  static std::shared_ptr<List<unsigned int>>
  sieve(const std::shared_ptr<List<unsigned int>> &l);
  /// run_length_encode l encodes consecutive runs: 1,1,2,3,3,3 ->
  /// (1,2),(2,1),(3,3).
  static std::shared_ptr<List<std::pair<unsigned int, unsigned int>>>
  run_length_encode(const std::shared_ptr<List<unsigned int>> &l);
  /// prefix_sums acc l cumulative sums: 1,2,3 with acc=0 -> 0,1,3,6.
  static std::shared_ptr<List<unsigned int>>
  prefix_sums(const unsigned int acc,
              const std::shared_ptr<List<unsigned int>> &l);
  /// differences l consecutive differences: 5,3,8,2 -> -2,5,-6.
  static std::shared_ptr<List<unsigned int>>
  differences(const std::shared_ptr<List<unsigned int>> &l);
  /// rotate_left n l rotates list left by n positions.
  static std::shared_ptr<List<unsigned int>>
  rotate_left_fuel(const unsigned int fuel, const unsigned int n,
                   std::shared_ptr<List<unsigned int>> l);
  static std::shared_ptr<List<unsigned int>>
  rotate_left(const unsigned int n,
              const std::shared_ptr<List<unsigned int>> &l);
  /// nub l removes ALL duplicates (not just consecutive): 1,2,1,3,2 -> 1,2,3.
  static std::shared_ptr<List<unsigned int>>
  nub_aux(const std::shared_ptr<List<unsigned int>> &l,
          const unsigned int fuel);
  static std::shared_ptr<List<unsigned int>>
  nub(const std::shared_ptr<List<unsigned int>> &l);
  /// Internal helpers for palindrome check.
  static std::shared_ptr<List<unsigned int>>
  rev_impl(std::shared_ptr<List<unsigned int>> acc,
           const std::shared_ptr<List<unsigned int>> &l);
  __attribute__((pure)) static bool
  list_eq_impl(const std::shared_ptr<List<unsigned int>> &l1,
               const std::shared_ptr<List<unsigned int>> &l2);
  /// is_palindrome l checks if list reads same forwards and backwards.
  __attribute__((pure)) static bool
  is_palindrome(const std::shared_ptr<List<unsigned int>> &l);
  /// windows n l sliding windows of size n: windows 2 1,2,3,4 ->
  /// [1,2],[2,3],[3,4].
  static std::shared_ptr<List<unsigned int>>
  take_impl(const unsigned int k, const std::shared_ptr<List<unsigned int>> &l);
  static std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>
  windows_aux(const unsigned int n, std::shared_ptr<List<unsigned int>> l,
              const unsigned int fuel);
  static std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>
  windows(const unsigned int n, std::shared_ptr<List<unsigned int>> l);
  /// sliding_pairs l returns consecutive pairs: 1,2,3,4 -> (1,2),(2,3),(3,4).
  static std::shared_ptr<List<std::pair<unsigned int, unsigned int>>>
  sliding_pairs(const std::shared_ptr<List<unsigned int>> &l);
  /// max_prefix_sum l maximum sum of prefix (Kadane-like pattern).
  __attribute__((pure)) static unsigned int
  max_prefix_sum(const std::shared_ptr<List<unsigned int>> &l);
  /// weighted_sum i l computes weighted sum with increasing index.
  __attribute__((pure)) static unsigned int
  weighted_sum(const unsigned int i,
               const std::shared_ptr<List<unsigned int>> &l);
  /// step_sum l sums with conditional doubling for odd numbers.
  __attribute__((pure)) static unsigned int
  step_sum(const std::shared_ptr<List<unsigned int>> &l);
  /// Helper: get head with default value.
  __attribute__((pure)) static unsigned int
  head_nat(const unsigned int d, const std::shared_ptr<List<unsigned int>> &l);
  /// suffix_sums l computes suffix sums (reverse of prefix sums).
  static std::shared_ptr<List<unsigned int>>
  suffix_sums(const std::shared_ptr<List<unsigned int>> &l);
};

#endif // INCLUDED_LOOPIFY_ALGORITHMS
