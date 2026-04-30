#ifndef INCLUDED_LOOPIFY_ALGORITHMS
#define INCLUDED_LOOPIFY_ALGORITHMS

#include <functional>
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

  List<t_A> app(List<t_A> m) const {
    std::unique_ptr<List<t_A>> _head{};
    std::unique_ptr<List<t_A>> *_write = &_head;
    const List *_loop_self = this;
    List<t_A> _loop_m = std::move(m);
    while (true) {
      auto &&_sv = *(_loop_self);
      if (std::holds_alternative<typename List<t_A>::Nil>(_sv.v())) {
        *(_write) = std::make_unique<List<t_A>>(std::move(_loop_m));
        break;
      } else {
        const auto &[d_a0, d_a1] = std::get<typename List<t_A>::Cons>(_sv.v());
        auto _cell = std::make_unique<List<t_A>>(
            typename List<t_A>::Cons(d_a0, nullptr));
        *(_write) = std::move(_cell);
        _write = &std::get<typename List<t_A>::Cons>((*_write)->v_mut()).d_a1;
        const List *_next_self = d_a1.get();
        List<t_A> _next_m = std::move(_loop_m);
        _loop_self = _next_self;
        _loop_m = std::move(_next_m);
        continue;
      }
    }
    return std::move(*(_head));
  }
};

/// Consolidated UNIQUE list/sequence algorithms.
struct LoopifyAlgorithms {
  static unsigned int len_impl(const List<unsigned int> &l);
  /// sieve l Sieve of Eratosthenes - filters out multiples.
  static List<unsigned int> sieve_fuel(const unsigned int &fuel,
                                       List<unsigned int> l);
  static List<unsigned int> sieve(const List<unsigned int> &l);
  /// run_length_encode l encodes consecutive runs: 1,1,2,3,3,3 ->
  /// (1,2),(2,1),(3,3).
  static List<std::pair<unsigned int, unsigned int>>
  run_length_encode(const List<unsigned int> &l);
  /// prefix_sums acc l cumulative sums: 1,2,3 with acc=0 -> 0,1,3,6.
  static List<unsigned int> prefix_sums(unsigned int acc,
                                        const List<unsigned int> &l);
  /// differences l consecutive differences: 5,3,8,2 -> -2,5,-6.
  static List<unsigned int> differences(const List<unsigned int> &l);
  /// rotate_left n l rotates list left by n positions.
  static List<unsigned int> rotate_left_fuel(const unsigned int &fuel,
                                             const unsigned int &n,
                                             List<unsigned int> l);
  static List<unsigned int> rotate_left(const unsigned int &n,
                                        const List<unsigned int> &l);
  /// nub l removes ALL duplicates (not just consecutive): 1,2,1,3,2 -> 1,2,3.
  static List<unsigned int> nub_aux(const List<unsigned int> &l,
                                    const unsigned int &fuel);
  static List<unsigned int> nub(const List<unsigned int> &l);
  /// Internal helpers for palindrome check.
  static List<unsigned int> rev_impl(List<unsigned int> acc,
                                     const List<unsigned int> &l);
  static bool list_eq_impl(const List<unsigned int> &l1,
                           const List<unsigned int> &l2);
  /// is_palindrome l checks if list reads same forwards and backwards.
  static bool is_palindrome(const List<unsigned int> &l);
  /// windows n l sliding windows of size n: windows 2 1,2,3,4 ->
  /// [1,2],[2,3],[3,4].
  static List<unsigned int> take_impl(const unsigned int &k,
                                      const List<unsigned int> &l);
  static List<List<unsigned int>> windows_aux(const unsigned int &n,
                                              const List<unsigned int> &l,
                                              const unsigned int &fuel);
  static List<List<unsigned int>> windows(const unsigned int &n,
                                          const List<unsigned int> &l);
  /// sliding_pairs l returns consecutive pairs: 1,2,3,4 -> (1,2),(2,3),(3,4).
  static List<std::pair<unsigned int, unsigned int>>
  sliding_pairs(const List<unsigned int> &l);
  /// max_prefix_sum l maximum sum of prefix (Kadane-like pattern).
  static unsigned int max_prefix_sum(const List<unsigned int> &l);
  /// weighted_sum i l computes weighted sum with increasing index.
  static unsigned int weighted_sum(unsigned int i, const List<unsigned int> &l);
  /// step_sum l sums with conditional doubling for odd numbers.
  static unsigned int step_sum(const List<unsigned int> &l);
  /// Helper: get head with default value.
  static unsigned int head_nat(unsigned int d, const List<unsigned int> &l);
  /// suffix_sums l computes suffix sums (reverse of prefix sums).
  static List<unsigned int> suffix_sums(const List<unsigned int> &l);
};

#endif // INCLUDED_LOOPIFY_ALGORITHMS
