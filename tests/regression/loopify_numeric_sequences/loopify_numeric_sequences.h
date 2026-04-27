#ifndef INCLUDED_LOOPIFY_NUMERIC_SEQUENCES
#define INCLUDED_LOOPIFY_NUMERIC_SEQUENCES

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
  using crane_element_type = t_A;

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

  __attribute__((pure)) List<t_A> &operator=(const List<t_A> &_other) {
    d_v_ = std::move(_other.clone().d_v_);
    return *this;
  }

  __attribute__((pure)) List<t_A> &operator=(List<t_A> &&_other) {
    d_v_ = std::move(_other.d_v_);
    return *this;
  }

  // ACCESSORS
  __attribute__((pure)) List<t_A> clone() const {
    auto &&_sv = *(this);
    if (std::holds_alternative<Nil>(_sv.v())) {
      return List<t_A>(Nil{});
    } else {
      const auto &[d_a0, d_a1] = std::get<Cons>(_sv.v());
      t_A __c0;
      if constexpr (
          requires { d_a0 ? 0 : 0; } && requires { *d_a0; } &&
          requires { d_a0->clone(); } && requires { d_a0.get(); }) {
        using _E = std::remove_cvref_t<decltype(*d_a0)>;
        __c0 = d_a0 ? std::make_unique<_E>(d_a0->clone()) : nullptr;
      } else if constexpr (requires { d_a0.clone(); }) {
        __c0 = d_a0.clone();
      } else {
        __c0 = d_a0;
      }
      return List<t_A>(
          Cons{std::move(__c0),
               d_a1 ? std::make_unique<List<t_A>>(d_a1->clone()) : nullptr});
    }
  }

  // CREATORS
  template <typename _U> explicit List(const List<_U> &_other) {
    if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
      d_v_ = Nil{};
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<_U>::Cons>(_other.v());
      d_v_ = Cons{
          [&]<typename _DstT = t_A>(auto &&__v) -> _DstT {
            if constexpr (
                requires { *__v; } &&
                !requires { std::declval<_DstT>().get(); })
              return _DstT(*__v);
            else if constexpr (
                !requires { *__v; } &&
                requires { std::declval<_DstT>().get(); }) {
              using _E =
                  std::remove_pointer_t<decltype(std::declval<_DstT>().get())>;
              return std::make_unique<_E>(std::move(__v));
            } else
              return _DstT(__v);
          }(d_a0),
          d_a1 ? std::make_unique<List<t_A>>(*d_a1) : nullptr};
    }
  }

  __attribute__((pure)) static List<t_A> nil() { return List(Nil{}); }

  __attribute__((pure)) static List<t_A> cons(t_A a0, const List<t_A> &a1) {
    return List(Cons{std::move(a0), std::make_unique<List<t_A>>(a1)});
  }

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) List<t_A> *operator->() { return this; }

  __attribute__((pure)) const List<t_A> *operator->() const { return this; }

  __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

  __attribute__((pure)) bool operator==(std::nullptr_t) const { return false; }

  // MANIPULATORS
  void reset() { *this = List<t_A>(); }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }
};

struct LoopifyNumericSequences {
  __attribute__((pure)) static unsigned int
  collatz_length_fuel(const unsigned int &fuel, const unsigned int &n);
  __attribute__((pure)) static unsigned int
  collatz_length(const unsigned int &n);
  __attribute__((pure)) static List<unsigned int>
  collatz_sequence_fuel(const unsigned int &fuel, unsigned int n);
  __attribute__((pure)) static List<unsigned int>
  collatz_sequence(const unsigned int &n);
  __attribute__((pure)) static unsigned int
  tribonacci_fuel(const unsigned int &fuel, const unsigned int &n);
  __attribute__((pure)) static unsigned int tribonacci(const unsigned int &n);
  __attribute__((pure)) static unsigned int
  staircase_fuel(const unsigned int &fuel, const unsigned int &n);
  __attribute__((pure)) static unsigned int staircase(const unsigned int &n);

  template <MapsTo<unsigned int, unsigned int> F1>
  __attribute__((pure)) static unsigned int church(const unsigned int &n,
                                                   F1 &&f, unsigned int x) {
    unsigned int _result;
    unsigned int _loop_x = std::move(x);
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
  digitsum_fuel(const unsigned int &fuel, const unsigned int &n);
  __attribute__((pure)) static unsigned int digitsum(const unsigned int &n);
  __attribute__((pure)) static unsigned int
  dec_to_bin_fuel(const unsigned int &fuel, const unsigned int &n);
  __attribute__((pure)) static unsigned int dec_to_bin(const unsigned int &n);
  __attribute__((pure)) static unsigned int
  alternate_sum(const bool &sign, unsigned int acc,
                const List<unsigned int> &l);
  __attribute__((pure)) static unsigned int
  sum_divisors_aux(const unsigned int &n, const unsigned int &d);
  __attribute__((pure)) static unsigned int sum_divisors(const unsigned int &n);
};

#endif // INCLUDED_LOOPIFY_NUMERIC_SEQUENCES
