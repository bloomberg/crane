#ifndef INCLUDED_BENCH_LET_IN
#define INCLUDED_BENCH_LET_IN

#include <type_traits>
#include <utility>
#include <variant>

struct BenchLetIn {
  template <typename A, typename B> struct pair {
    // TYPES
    struct Pair0 {
      A a0;
      B a1;
    };

    using variant_t = std::variant<Pair0>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    pair() {}

    explicit pair(Pair0 _v) : v_(std::move(_v)) {}

    pair(const pair<A, B> &_other) : v_(std::move(_other.clone().v_)) {}

    pair(pair<A, B> &&_other) : v_(std::move(_other.v_)) {}

    pair<A, B> &operator=(const pair<A, B> &_other) {
      v_ = std::move(_other.clone().v_);
      return *this;
    }

    pair<A, B> &operator=(pair<A, B> &&_other) {
      v_ = std::move(_other.v_);
      return *this;
    }

    // ACCESSORS
    pair<A, B> clone() const {
      const auto &[a0, a1] = std::get<Pair0>(this->v());
      return pair<A, B>(Pair0{a0, a1});
    }

    // CREATORS
    template <typename _U0, typename _U1>
    explicit pair(const pair<_U0, _U1> &_other) {
      const auto &[a0, a1] =
          std::get<typename pair<_U0, _U1>::Pair0>(_other.v());
      this->v_ = Pair0{A(a0), B(a1)};
    }

    static pair<A, B> pair0(A a0, B a1) {
      return pair(Pair0{std::move(a0), std::move(a1)});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    template <typename T1, typename F0>
      requires std::is_invocable_r_v<T1, F0 &, A &, B &>
    T1 pair_rec(F0 &&f) const {
      const auto &[a0, a1] = std::get<typename pair<A, B>::Pair0>(this->v());
      return f(a0, a1);
    }

    template <typename T1, typename F0>
      requires std::is_invocable_r_v<T1, F0 &, A &, B &>
    T1 pair_rect(F0 &&f) const {
      const auto &[a0, a1] = std::get<typename pair<A, B>::Pair0>(this->v());
      return f(a0, a1);
    }
  };

  static unsigned int swap_snd(unsigned int a, unsigned int b);
  static unsigned int add_via_pair(unsigned int a, unsigned int b);
  static unsigned int nested_swap(unsigned int a, unsigned int b,
                                  unsigned int c, unsigned int d);
  static unsigned int sum_via_pairs(unsigned int n);

  template <typename A, typename B, typename C> struct triple {
    // TYPES
    struct Triple0 {
      A a0;
      B a1;
      C a2;
    };

    using variant_t = std::variant<Triple0>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    triple() {}

    explicit triple(Triple0 _v) : v_(std::move(_v)) {}

    triple(const triple<A, B, C> &_other) : v_(std::move(_other.clone().v_)) {}

    triple(triple<A, B, C> &&_other) : v_(std::move(_other.v_)) {}

    triple<A, B, C> &operator=(const triple<A, B, C> &_other) {
      v_ = std::move(_other.clone().v_);
      return *this;
    }

    triple<A, B, C> &operator=(triple<A, B, C> &&_other) {
      v_ = std::move(_other.v_);
      return *this;
    }

    // ACCESSORS
    triple<A, B, C> clone() const {
      const auto &[a0, a1, a2] = std::get<Triple0>(this->v());
      return triple<A, B, C>(Triple0{a0, a1, a2});
    }

    // CREATORS
    template <typename _U0, typename _U1, typename _U2>
    explicit triple(const triple<_U0, _U1, _U2> &_other) {
      const auto &[a0, a1, a2] =
          std::get<typename triple<_U0, _U1, _U2>::Triple0>(_other.v());
      this->v_ = Triple0{A(a0), B(a1), C(a2)};
    }

    static triple<A, B, C> triple0(A a0, B a1, C a2) {
      return triple(Triple0{std::move(a0), std::move(a1), std::move(a2)});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    template <typename T1, typename F0>
      requires std::is_invocable_r_v<T1, F0 &, A &, B &, C &>
    T1 triple_rec(F0 &&f) const {
      const auto &[a0, a1, a2] =
          std::get<typename triple<A, B, C>::Triple0>(this->v());
      return f(a0, a1, a2);
    }

    template <typename T1, typename F0>
      requires std::is_invocable_r_v<T1, F0 &, A &, B &, C &>
    T1 triple_rect(F0 &&f) const {
      const auto &[a0, a1, a2] =
          std::get<typename triple<A, B, C>::Triple0>(this->v());
      return f(a0, a1, a2);
    }
  };

  static unsigned int mid3(unsigned int a, unsigned int b, unsigned int c);
  static unsigned int sum3(unsigned int a, unsigned int b, unsigned int c);
  static unsigned int chain_pairs(unsigned int a, unsigned int b,
                                  unsigned int c);
  static inline const unsigned int test_swap = swap_snd(3u, 4u);
  static inline const unsigned int test_add = add_via_pair(3u, 4u);
  static inline const unsigned int test_nested = nested_swap(1u, 2u, 3u, 4u);
  static inline const unsigned int test_sum_pairs = sum_via_pairs(5u);
  static inline const unsigned int test_mid3 = mid3(1u, 2u, 3u);
  static inline const unsigned int test_sum3 = sum3(1u, 2u, 3u);
  static inline const unsigned int test_chain = chain_pairs(1u, 2u, 3u);
};

#endif // INCLUDED_BENCH_LET_IN
