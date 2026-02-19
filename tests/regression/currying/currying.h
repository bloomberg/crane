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

struct Currying {
  static unsigned int add3(const unsigned int a, const unsigned int b,
                           const unsigned int c);

  static unsigned int add3_partial1(const unsigned int, const unsigned int);

  static unsigned int add3_partial2(const unsigned int);

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

  template <typename T1, typename T2, typename T3,
            MapsTo<T3, std::shared_ptr<pair<T1, T2>>> F0>
  static T3 curry(F0 &&f, const T1 a, const T2 b) {
    return f(pair<T1, T2>::ctor::Pair_(a, b));
  }

  template <typename T1, typename T2, typename T3, MapsTo<T3, T1, T2> F0>
  static T3 uncurry(F0 &&f, const std::shared_ptr<pair<T1, T2>> &p) {
    return std::visit(
        Overloaded{[&](const typename pair<T1, T2>::Pair _args) -> T3 {
          T1 a = _args._a0;
          T2 b = _args._a1;
          return f(a, b);
        }},
        p->v());
  }

  static unsigned int
  pair_add(const std::shared_ptr<pair<unsigned int, unsigned int>> &p);

  static unsigned int curried_add(const unsigned int, const unsigned int);

  static unsigned int uncurried_add3(
      const std::shared_ptr<
          pair<unsigned int, std::shared_ptr<pair<unsigned int, unsigned int>>>>
          &p);

  template <typename T1, typename T2, typename T3, MapsTo<T3, T1, T2> F0>
  static T3 flip(F0 &&f, const T2 b, const T1 a) {
    return f(a, b);
  }

  static unsigned int sub(const unsigned int, const unsigned int);

  static unsigned int flipped_sub(const unsigned int, const unsigned int);

  static unsigned int add_base(const unsigned int, const unsigned int);

  static unsigned int add_ten(const unsigned int);

  static inline const unsigned int test_add3 = add3(1u, 2u, 3u);

  static inline const unsigned int test_partial1 = add3_partial1(2u, 3u);

  static inline const unsigned int test_partial2 = add3_partial2(3u);

  static inline const unsigned int test_curried = curried_add(3u, 4u);

  static inline const unsigned int test_flip = flipped_sub(3u, 7u);

  static inline const unsigned int test_add_ten = add_ten(5u);
};
