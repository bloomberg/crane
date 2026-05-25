#ifndef INCLUDED_LOOPIFY_ALGORITHMS
#define INCLUDED_LOOPIFY_ALGORITHMS

#include <any>
#include <memory>
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

  List<A> app(List<A> m) const {
    if (std::holds_alternative<typename List<A>::Nil>(this->v())) {
      return m;
    } else {
      const auto &[a0, a1] = std::get<typename List<A>::Cons>(this->v());
      return List<A>::cons(a0, a1->app(std::move(m)));
    }
  }
};

/// Consolidated UNIQUE list/sequence algorithms.
struct LoopifyAlgorithms {
  static uint64_t len_impl(const List<uint64_t> &l);
  /// sieve l Sieve of Eratosthenes - filters out multiples.
  static List<uint64_t> sieve_fuel(uint64_t fuel, List<uint64_t> l);
  static List<uint64_t> sieve(const List<uint64_t> &l);
  /// run_length_encode l encodes consecutive runs: 1,1,2,3,3,3 ->
  /// (1,2),(2,1),(3,3).
  static List<std::pair<uint64_t, uint64_t>>
  run_length_encode(const List<uint64_t> &l);
  /// prefix_sums acc l cumulative sums: 1,2,3 with acc=0 -> 0,1,3,6.
  static List<uint64_t> prefix_sums(uint64_t acc, const List<uint64_t> &l);
  /// differences l consecutive differences: 5,3,8,2 -> -2,5,-6.
  static List<uint64_t> differences(const List<uint64_t> &l);
  /// rotate_left n l rotates list left by n positions.
  static List<uint64_t> rotate_left_fuel(uint64_t fuel, uint64_t n,
                                         List<uint64_t> l);
  static List<uint64_t> rotate_left(uint64_t n, const List<uint64_t> &l);
  /// nub l removes ALL duplicates (not just consecutive): 1,2,1,3,2 -> 1,2,3.
  static List<uint64_t> nub_aux(const List<uint64_t> &l, uint64_t fuel);
  static List<uint64_t> nub(const List<uint64_t> &l);
  /// Internal helpers for palindrome check.
  static List<uint64_t> rev_impl(List<uint64_t> acc, const List<uint64_t> &l);
  static bool list_eq_impl(const List<uint64_t> &l1, const List<uint64_t> &l2);
  /// is_palindrome l checks if list reads same forwards and backwards.
  static bool is_palindrome(const List<uint64_t> &l);
  /// windows n l sliding windows of size n: windows 2 1,2,3,4 ->
  /// [1,2],[2,3],[3,4].
  static List<uint64_t> take_impl(uint64_t k, const List<uint64_t> &l);
  static List<List<uint64_t>> windows_aux(uint64_t n, const List<uint64_t> &l,
                                          uint64_t fuel);
  static List<List<uint64_t>> windows(uint64_t n, const List<uint64_t> &l);
  /// sliding_pairs l returns consecutive pairs: 1,2,3,4 -> (1,2),(2,3),(3,4).
  static List<std::pair<uint64_t, uint64_t>>
  sliding_pairs(const List<uint64_t> &l);
  /// max_prefix_sum l maximum sum of prefix (Kadane-like pattern).
  static uint64_t max_prefix_sum(const List<uint64_t> &l);
  /// weighted_sum i l computes weighted sum with increasing index.
  static uint64_t weighted_sum(uint64_t i, const List<uint64_t> &l);
  /// step_sum l sums with conditional doubling for odd numbers.
  static uint64_t step_sum(const List<uint64_t> &l);
  /// Helper: get head with default value.
  static uint64_t head_nat(uint64_t d, const List<uint64_t> &l);
  /// suffix_sums l computes suffix sums (reverse of prefix sums).
  static List<uint64_t> suffix_sums(const List<uint64_t> &l);
};

#endif // INCLUDED_LOOPIFY_ALGORITHMS
