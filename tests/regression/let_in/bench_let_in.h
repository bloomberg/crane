#ifndef INCLUDED_BENCH_LET_IN
#define INCLUDED_BENCH_LET_IN

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

struct BenchLetIn {
  template <typename t_A, typename t_B> struct pair {
    // TYPES
    struct Pair0 {
      t_A d_a0;
      t_B d_a1;
    };

    using variant_t = std::variant<Pair0>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    pair() {}

    explicit pair(Pair0 _v) : d_v_(std::move(_v)) {}

    pair(const pair<t_A, t_B> &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    pair(pair<t_A, t_B> &&_other) : d_v_(std::move(_other.d_v_)) {}

    pair<t_A, t_B> &operator=(const pair<t_A, t_B> &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    pair<t_A, t_B> &operator=(pair<t_A, t_B> &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) pair<t_A, t_B> clone() const {
      auto &&_sv = *(this);
      const auto &[d_a0, d_a1] = std::get<Pair0>(_sv.v());
      return pair<t_A, t_B>(Pair0{d_a0, d_a1});
    }

    // CREATORS
    template <typename _U0, typename _U1>
    explicit pair(const pair<_U0, _U1> &_other) {
      const auto &[d_a0, d_a1] =
          std::get<typename pair<_U0, _U1>::Pair0>(_other.v());
      d_v_ = Pair0{t_A(d_a0), t_B(d_a1)};
    }

    __attribute__((pure)) static pair<t_A, t_B> pair0(t_A a0, t_B a1) {
      return pair(Pair0{std::move(a0), std::move(a1)});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    template <typename T1, MapsTo<T1, t_A, t_B> F0> T1 pair_rec(F0 &&f) const {
      auto &&_sv = *(this);
      const auto &[d_a0, d_a1] =
          std::get<typename pair<t_A, t_B>::Pair0>(_sv.v());
      return f(d_a0, d_a1);
    }

    template <typename T1, MapsTo<T1, t_A, t_B> F0> T1 pair_rect(F0 &&f) const {
      auto &&_sv = *(this);
      const auto &[d_a0, d_a1] =
          std::get<typename pair<t_A, t_B>::Pair0>(_sv.v());
      return f(d_a0, d_a1);
    }
  };

  __attribute__((pure)) static unsigned int swap_snd(unsigned int a,
                                                     unsigned int b);
  __attribute__((pure)) static unsigned int add_via_pair(unsigned int a,
                                                         unsigned int b);
  __attribute__((pure)) static unsigned int
  nested_swap(unsigned int a, unsigned int b, unsigned int c, unsigned int d);
  __attribute__((pure)) static unsigned int sum_via_pairs(unsigned int n);

  template <typename t_A, typename t_B, typename t_C> struct triple {
    // TYPES
    struct Triple0 {
      t_A d_a0;
      t_B d_a1;
      t_C d_a2;
    };

    using variant_t = std::variant<Triple0>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    triple() {}

    explicit triple(Triple0 _v) : d_v_(std::move(_v)) {}

    triple(const triple<t_A, t_B, t_C> &_other)
        : d_v_(std::move(_other.clone().d_v_)) {}

    triple(triple<t_A, t_B, t_C> &&_other) : d_v_(std::move(_other.d_v_)) {}

    triple<t_A, t_B, t_C> &operator=(const triple<t_A, t_B, t_C> &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    triple<t_A, t_B, t_C> &operator=(triple<t_A, t_B, t_C> &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) triple<t_A, t_B, t_C> clone() const {
      auto &&_sv = *(this);
      const auto &[d_a0, d_a1, d_a2] = std::get<Triple0>(_sv.v());
      return triple<t_A, t_B, t_C>(Triple0{d_a0, d_a1, d_a2});
    }

    // CREATORS
    template <typename _U0, typename _U1, typename _U2>
    explicit triple(const triple<_U0, _U1, _U2> &_other) {
      const auto &[d_a0, d_a1, d_a2] =
          std::get<typename triple<_U0, _U1, _U2>::Triple0>(_other.v());
      d_v_ = Triple0{t_A(d_a0), t_B(d_a1), t_C(d_a2)};
    }

    __attribute__((pure)) static triple<t_A, t_B, t_C> triple0(t_A a0, t_B a1,
                                                               t_C a2) {
      return triple(Triple0{std::move(a0), std::move(a1), std::move(a2)});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    template <typename T1, MapsTo<T1, t_A, t_B, t_C> F0>
    T1 triple_rec(F0 &&f) const {
      auto &&_sv = *(this);
      const auto &[d_a0, d_a1, d_a2] =
          std::get<typename triple<t_A, t_B, t_C>::Triple0>(_sv.v());
      return f(d_a0, d_a1, d_a2);
    }

    template <typename T1, MapsTo<T1, t_A, t_B, t_C> F0>
    T1 triple_rect(F0 &&f) const {
      auto &&_sv = *(this);
      const auto &[d_a0, d_a1, d_a2] =
          std::get<typename triple<t_A, t_B, t_C>::Triple0>(_sv.v());
      return f(d_a0, d_a1, d_a2);
    }
  };

  __attribute__((pure)) static unsigned int mid3(unsigned int a, unsigned int b,
                                                 unsigned int c);
  __attribute__((pure)) static unsigned int sum3(unsigned int a, unsigned int b,
                                                 unsigned int c);
  __attribute__((pure)) static unsigned int
  chain_pairs(unsigned int a, unsigned int b, unsigned int c);
  static inline const unsigned int test_swap = swap_snd(3u, 4u);
  static inline const unsigned int test_add = add_via_pair(3u, 4u);
  static inline const unsigned int test_nested = nested_swap(1u, 2u, 3u, 4u);
  static inline const unsigned int test_sum_pairs = sum_via_pairs(5u);
  static inline const unsigned int test_mid3 = mid3(1u, 2u, 3u);
  static inline const unsigned int test_sum3 = sum3(1u, 2u, 3u);
  static inline const unsigned int test_chain = chain_pairs(1u, 2u, 3u);
};

#endif // INCLUDED_BENCH_LET_IN
