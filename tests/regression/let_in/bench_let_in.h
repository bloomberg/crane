#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

struct BenchLetIn {
  template <typename A, typename B> struct pair {
  public:
    struct Pair {
      A _a0;
      B _a1;
    };
    using variant_t = std::variant<Pair>;

  private:
    variant_t v_;
    explicit pair(Pair _v) : v_(std::move(_v)) {}

  public:
    struct ctor {
      ctor() = delete;
      static std::shared_ptr<pair<A, B>> Pair_(A a0, B a1) {
        return std::shared_ptr<pair<A, B>>(new pair<A, B>(Pair{a0, a1}));
      }
      static std::unique_ptr<pair<A, B>> Pair_uptr(A a0, B a1) {
        return std::unique_ptr<pair<A, B>>(new pair<A, B>(Pair{a0, a1}));
      }
    };
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename T2, typename T3, MapsTo<T3, T1, T2> F0>
  static T3 pair_rect(F0 &&f, const std::shared_ptr<pair<T1, T2>> &p) {
    return std::visit(
        Overloaded{[&](const typename pair<T1, T2>::Pair _args) -> T3 {
          T1 a = _args._a0;
          T2 b = _args._a1;
          return f(a, b);
        }},
        p->v());
  }

  template <typename T1, typename T2, typename T3, MapsTo<T3, T1, T2> F0>
  static T3 pair_rec(F0 &&f, const std::shared_ptr<pair<T1, T2>> &p) {
    return std::visit(
        Overloaded{[&](const typename pair<T1, T2>::Pair _args) -> T3 {
          T1 a = _args._a0;
          T2 b = _args._a1;
          return f(a, b);
        }},
        p->v());
  }

  static unsigned int swap_snd(const unsigned int a, const unsigned int b);

  static unsigned int add_via_pair(const unsigned int a, const unsigned int b);

  static unsigned int nested_swap(const unsigned int a, const unsigned int b,
                                  const unsigned int c, const unsigned int d);

  static unsigned int sum_via_pairs(const unsigned int n);

  template <typename A, typename B, typename C> struct triple {
  public:
    struct Triple {
      A _a0;
      B _a1;
      C _a2;
    };
    using variant_t = std::variant<Triple>;

  private:
    variant_t v_;
    explicit triple(Triple _v) : v_(std::move(_v)) {}

  public:
    struct ctor {
      ctor() = delete;
      static std::shared_ptr<triple<A, B, C>> Triple_(A a0, B a1, C a2) {
        return std::shared_ptr<triple<A, B, C>>(
            new triple<A, B, C>(Triple{a0, a1, a2}));
      }
      static std::unique_ptr<triple<A, B, C>> Triple_uptr(A a0, B a1, C a2) {
        return std::unique_ptr<triple<A, B, C>>(
            new triple<A, B, C>(Triple{a0, a1, a2}));
      }
    };
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename T2, typename T3, typename T4,
            MapsTo<T4, T1, T2, T3> F0>
  static T4 triple_rect(F0 &&f, const std::shared_ptr<triple<T1, T2, T3>> &t) {
    return std::visit(
        Overloaded{[&](const typename triple<T1, T2, T3>::Triple _args) -> T4 {
          T1 a = _args._a0;
          T2 b = _args._a1;
          T3 c = _args._a2;
          return f(a, b, c);
        }},
        t->v());
  }

  template <typename T1, typename T2, typename T3, typename T4,
            MapsTo<T4, T1, T2, T3> F0>
  static T4 triple_rec(F0 &&f, const std::shared_ptr<triple<T1, T2, T3>> &t) {
    return std::visit(
        Overloaded{[&](const typename triple<T1, T2, T3>::Triple _args) -> T4 {
          T1 a = _args._a0;
          T2 b = _args._a1;
          T3 c = _args._a2;
          return f(a, b, c);
        }},
        t->v());
  }

  static unsigned int mid3(const unsigned int a, const unsigned int b,
                           const unsigned int c);

  static unsigned int sum3(const unsigned int a, const unsigned int b,
                           const unsigned int c);

  static unsigned int chain_pairs(const unsigned int a, const unsigned int b,
                                  const unsigned int c);

  static inline const unsigned int test_swap =
      swap_snd((((0 + 1) + 1) + 1), ((((0 + 1) + 1) + 1) + 1));

  static inline const unsigned int test_add =
      add_via_pair((((0 + 1) + 1) + 1), ((((0 + 1) + 1) + 1) + 1));

  static inline const unsigned int test_nested = nested_swap(
      (0 + 1), ((0 + 1) + 1), (((0 + 1) + 1) + 1), ((((0 + 1) + 1) + 1) + 1));

  static inline const unsigned int test_sum_pairs =
      sum_via_pairs((((((0 + 1) + 1) + 1) + 1) + 1));

  static inline const unsigned int test_mid3 =
      mid3((0 + 1), ((0 + 1) + 1), (((0 + 1) + 1) + 1));

  static inline const unsigned int test_sum3 =
      sum3((0 + 1), ((0 + 1) + 1), (((0 + 1) + 1) + 1));

  static inline const unsigned int test_chain =
      chain_pairs((0 + 1), ((0 + 1) + 1), (((0 + 1) + 1) + 1));
};
