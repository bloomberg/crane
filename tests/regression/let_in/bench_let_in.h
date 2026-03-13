#ifndef INCLUDED_BENCH_LET_IN
#define INCLUDED_BENCH_LET_IN

#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

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

    // CREATORS
    explicit pair(Pair0 _v) : d_v_(std::move(_v)) {}

  public:
    // TYPES
    struct ctor {
      ctor() = delete;

      static std::shared_ptr<pair<t_A, t_B>> Pair0_(t_A a0, t_B a1) {
        return std::shared_ptr<pair<t_A, t_B>>(
            new pair<t_A, t_B>(Pair0{a0, a1}));
      }

      static std::unique_ptr<pair<t_A, t_B>> Pair0_uptr(t_A a0, t_B a1) {
        return std::unique_ptr<pair<t_A, t_B>>(
            new pair<t_A, t_B>(Pair0{a0, a1}));
      }
    };

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, typename T2, typename T3, MapsTo<T3, T1, T2> F0>
  static T3 pair_rect(F0 &&f, const std::shared_ptr<pair<T1, T2>> &p) {
    return std::visit(
        Overloaded{[&](const typename pair<T1, T2>::Pair0 _args) -> T3 {
          T1 a = _args.d_a0;
          T2 b = _args.d_a1;
          return f(a, b);
        }},
        p->v());
  }

  template <typename T1, typename T2, typename T3, MapsTo<T3, T1, T2> F0>
  static T3 pair_rec(F0 &&f, const std::shared_ptr<pair<T1, T2>> &p) {
    return std::visit(
        Overloaded{[&](const typename pair<T1, T2>::Pair0 _args) -> T3 {
          T1 a = _args.d_a0;
          T2 b = _args.d_a1;
          return f(a, b);
        }},
        p->v());
  }

  __attribute__((pure)) static unsigned int swap_snd(const unsigned int a,
                                                     const unsigned int b);
  __attribute__((pure)) static unsigned int add_via_pair(const unsigned int a,
                                                         const unsigned int b);
  __attribute__((pure)) static unsigned int nested_swap(const unsigned int a,
                                                        const unsigned int b,
                                                        const unsigned int c,
                                                        const unsigned int d);
  __attribute__((pure)) static unsigned int sum_via_pairs(const unsigned int n);

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

    // CREATORS
    explicit triple(Triple0 _v) : d_v_(std::move(_v)) {}

  public:
    // TYPES
    struct ctor {
      ctor() = delete;

      static std::shared_ptr<triple<t_A, t_B, t_C>> Triple0_(t_A a0, t_B a1,
                                                             t_C a2) {
        return std::shared_ptr<triple<t_A, t_B, t_C>>(
            new triple<t_A, t_B, t_C>(Triple0{a0, a1, a2}));
      }

      static std::unique_ptr<triple<t_A, t_B, t_C>> Triple0_uptr(t_A a0, t_B a1,
                                                                 t_C a2) {
        return std::unique_ptr<triple<t_A, t_B, t_C>>(
            new triple<t_A, t_B, t_C>(Triple0{a0, a1, a2}));
      }
    };

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, typename T2, typename T3, typename T4,
            MapsTo<T4, T1, T2, T3> F0>
  static T4 triple_rect(F0 &&f, const std::shared_ptr<triple<T1, T2, T3>> &t) {
    return std::visit(
        Overloaded{[&](const typename triple<T1, T2, T3>::Triple0 _args) -> T4 {
          T1 a = _args.d_a0;
          T2 b = _args.d_a1;
          T3 c = _args.d_a2;
          return f(a, b, c);
        }},
        t->v());
  }

  template <typename T1, typename T2, typename T3, typename T4,
            MapsTo<T4, T1, T2, T3> F0>
  static T4 triple_rec(F0 &&f, const std::shared_ptr<triple<T1, T2, T3>> &t) {
    return std::visit(
        Overloaded{[&](const typename triple<T1, T2, T3>::Triple0 _args) -> T4 {
          T1 a = _args.d_a0;
          T2 b = _args.d_a1;
          T3 c = _args.d_a2;
          return f(a, b, c);
        }},
        t->v());
  }

  __attribute__((pure)) static unsigned int
  mid3(const unsigned int a, const unsigned int b, const unsigned int c);
  __attribute__((pure)) static unsigned int
  sum3(const unsigned int a, const unsigned int b, const unsigned int c);
  __attribute__((pure)) static unsigned int
  chain_pairs(const unsigned int a, const unsigned int b, const unsigned int c);
  static inline const unsigned int test_swap = swap_snd(3u, 4u);
  static inline const unsigned int test_add = add_via_pair(3u, 4u);
  static inline const unsigned int test_nested = nested_swap(1u, 2u, 3u, 4u);
  static inline const unsigned int test_sum_pairs = sum_via_pairs(5u);
  static inline const unsigned int test_mid3 = mid3(1u, 2u, 3u);
  static inline const unsigned int test_sum3 = sum3(1u, 2u, 3u);
  static inline const unsigned int test_chain = chain_pairs(1u, 2u, 3u);
};

#endif // INCLUDED_BENCH_LET_IN
