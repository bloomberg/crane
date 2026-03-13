#ifndef INCLUDED_LET_IN
#define INCLUDED_LET_IN

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

struct LetIn {
  static inline const unsigned int simple_let = 5u;
  static inline const unsigned int nested_let = 3u;
  static inline const unsigned int let_with_add = [](void) {
    unsigned int x = 3u;
    unsigned int y = 4u;
    return (std::move(x) + std::move(y));
  }();
  static inline const unsigned int shadowed_let = 3u;
  __attribute__((pure)) static unsigned int let_in_fun(const unsigned int n);
  static inline const unsigned int let_fun = [](void) {
    unsigned int x = 5u;
    return (std::move(x) + 1u);
  }();

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

  static inline const unsigned int let_destruct = [](void) {
    std::unique_ptr<pair<unsigned int, unsigned int>> p =
        pair<unsigned int, unsigned int>::ctor::Pair0_uptr(3u, 4u);
    return std::visit(
        Overloaded{
            [](const typename pair<unsigned int, unsigned int>::Pair0 _args)
                -> unsigned int {
              unsigned int x = _args.d_a0;
              return std::move(x);
            }},
        std::move(p)->v());
  }();
  static inline const unsigned int multi_let = [](void) {
    unsigned int a = 1u;
    unsigned int b = 2u;
    unsigned int c = 3u;
    return (std::move(a) + (std::move(b) + std::move(c)));
  }();
  static inline const unsigned int test_simple = simple_let;
  static inline const unsigned int test_nested = nested_let;
  static inline const unsigned int test_add = let_with_add;
  static inline const unsigned int test_shadow = shadowed_let;
  static inline const unsigned int test_fun_call = let_in_fun(3u);
  static inline const unsigned int test_let_fun = let_fun;
  static inline const unsigned int test_destruct = let_destruct;
  static inline const unsigned int test_multi = multi_let;
};

#endif // INCLUDED_LET_IN
