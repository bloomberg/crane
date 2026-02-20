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

struct LetIn {
  static inline const unsigned int simple_let = 5u;

  static inline const unsigned int nested_let = 3u;

  static inline const unsigned int let_with_add = (3u + 4u);

  static inline const unsigned int shadowed_let = 3u;

  static unsigned int let_in_fun(const unsigned int n);

  static inline const unsigned int let_fun = (5u + 1u);

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

  static inline const unsigned int let_destruct = [](void) {
    std::unique_ptr<pair<unsigned int, unsigned int>> p =
        pair<unsigned int, unsigned int>::ctor::Pair_uptr(3u, 4u);
    return std::visit(
        Overloaded{
            [](const typename pair<unsigned int, unsigned int>::Pair _args)
                -> unsigned int {
              unsigned int x = _args._a0;
              return x;
            }},
        p->v());
  }();

  static inline const unsigned int multi_let = (1u + (2u + 3u));

  static inline const unsigned int test_simple = simple_let;

  static inline const unsigned int test_nested = nested_let;

  static inline const unsigned int test_add = let_with_add;

  static inline const unsigned int test_shadow = shadowed_let;

  static inline const unsigned int test_fun_call = let_in_fun(3u);

  static inline const unsigned int test_let_fun = let_fun;

  static inline const unsigned int test_destruct = let_destruct;

  static inline const unsigned int test_multi = multi_let;
};
