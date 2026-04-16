#ifndef INCLUDED_LOOPIFY_NUMERIC_SEQUENCES
#define INCLUDED_LOOPIFY_NUMERIC_SEQUENCES

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

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
  explicit List(Nil _v) : d_v_(_v) {}

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
};

struct LoopifyNumericSequences {
  __attribute__((pure)) static unsigned int
  collatz_length_fuel(const unsigned int fuel, const unsigned int n);
  __attribute__((pure)) static unsigned int
  collatz_length(const unsigned int n);
  static std::shared_ptr<List<unsigned int>>
  collatz_sequence_fuel(const unsigned int fuel, const unsigned int n);
  static std::shared_ptr<List<unsigned int>>
  collatz_sequence(const unsigned int n);
  __attribute__((pure)) static unsigned int
  tribonacci_fuel(const unsigned int fuel, const unsigned int n);
  __attribute__((pure)) static unsigned int tribonacci(const unsigned int n);
  __attribute__((pure)) static unsigned int
  staircase_fuel(const unsigned int fuel, const unsigned int n);
  __attribute__((pure)) static unsigned int staircase(const unsigned int n);

  template <MapsTo<unsigned int, unsigned int> F1>
  __attribute__((pure)) static unsigned int church(const unsigned int n, F1 &&f,
                                                   const unsigned int x) {
    unsigned int _result;
    unsigned int _loop_x = x;
    unsigned int _loop_n = n;
    while (true) {
      if (_loop_n <= 0) {
        _result = _loop_x;
        break;
      } else {
        unsigned int n_ = _loop_n - 1;
        unsigned int _next_x = f(_loop_x);
        unsigned int _next_n = n_;
        _loop_x = std::move(_next_x);
        _loop_n = std::move(_next_n);
      }
    }
    return _result;
  }

  __attribute__((pure)) static unsigned int
  digitsum_fuel(const unsigned int fuel, const unsigned int n);
  __attribute__((pure)) static unsigned int digitsum(const unsigned int n);
  __attribute__((pure)) static unsigned int
  dec_to_bin_fuel(const unsigned int fuel, const unsigned int n);
  __attribute__((pure)) static unsigned int dec_to_bin(const unsigned int n);
  __attribute__((pure)) static unsigned int
  alternate_sum(const bool sign, const unsigned int acc,
                const std::shared_ptr<List<unsigned int>> &l);
  __attribute__((pure)) static unsigned int
  sum_divisors_aux(const unsigned int n, const unsigned int d);
  __attribute__((pure)) static unsigned int sum_divisors(const unsigned int n);
};

#endif // INCLUDED_LOOPIFY_NUMERIC_SEQUENCES
