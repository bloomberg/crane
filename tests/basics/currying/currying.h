#ifndef INCLUDED_CURRYING
#define INCLUDED_CURRYING

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

struct Currying {
  __attribute__((pure)) static unsigned int
  add3(const unsigned int a, const unsigned int b, const unsigned int c);
  __attribute__((pure)) static unsigned int
  add3_partial1(const unsigned int _x0, const unsigned int _x1);
  __attribute__((pure)) static unsigned int
  add3_partial2(const unsigned int _x0);

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

  template <typename T1, typename T2, typename T3,
            MapsTo<T3, std::shared_ptr<pair<T1, T2>>> F0>
  static T3 curry(F0 &&f, const T1 a, const T2 b) {
    return f(pair<T1, T2>::ctor::Pair0_(a, b));
  }

  template <typename T1, typename T2, typename T3, MapsTo<T3, T1, T2> F0>
  static T3 uncurry(F0 &&f, const std::shared_ptr<pair<T1, T2>> &p) {
    return std::visit(
        Overloaded{[&](const typename pair<T1, T2>::Pair0 _args) -> T3 {
          T1 a = _args.d_a0;
          T2 b = _args.d_a1;
          return f(a, b);
        }},
        p->v());
  }

  __attribute__((pure)) static unsigned int
  pair_add(const std::shared_ptr<pair<unsigned int, unsigned int>> &p);
  __attribute__((pure)) static unsigned int curried_add(const unsigned int _x0,
                                                        const unsigned int _x1);
  __attribute__((pure)) static unsigned int uncurried_add3(
      const std::shared_ptr<
          pair<unsigned int, std::shared_ptr<pair<unsigned int, unsigned int>>>>
          &p);

  template <typename T1, typename T2, typename T3, MapsTo<T3, T1, T2> F0>
  static T3 flip(F0 &&f, const T2 b, const T1 a) {
    return f(a, b);
  }

  __attribute__((pure)) static unsigned int sub(const unsigned int _x0,
                                                const unsigned int _x1);
  __attribute__((pure)) static unsigned int flipped_sub(const unsigned int _x0,
                                                        const unsigned int _x1);
  __attribute__((pure)) static unsigned int add_base(const unsigned int _x0,
                                                     const unsigned int _x1);
  __attribute__((pure)) static unsigned int add_ten(const unsigned int _x0);
  static inline const unsigned int test_add3 = add3(1u, 2u, 3u);
  static inline const unsigned int test_partial1 = add3_partial1(2u, 3u);
  static inline const unsigned int test_partial2 = add3_partial2(3u);
  static inline const unsigned int test_curried = curried_add(3u, 4u);
  static inline const unsigned int test_flip = flipped_sub(3u, 7u);
  static inline const unsigned int test_add_ten = add_ten(5u);
};

#endif // INCLUDED_CURRYING
