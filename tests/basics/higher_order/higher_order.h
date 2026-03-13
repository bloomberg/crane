#ifndef INCLUDED_HIGHER_ORDER
#define INCLUDED_HIGHER_ORDER

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

struct HigherOrder {
  /// A simple polymorphic list type.
  template <typename t_A> struct list {
    // TYPES
    struct Nil {};

    struct Cons {
      t_A d_a0;
      std::shared_ptr<list<t_A>> d_a1;
    };

    using variant_t = std::variant<Nil, Cons>;

  private:
    // DATA
    variant_t d_v_;

    // CREATORS
    explicit list(Nil _v) : d_v_(std::move(_v)) {}

    explicit list(Cons _v) : d_v_(std::move(_v)) {}

  public:
    // TYPES
    struct ctor {
      ctor() = delete;

      static std::shared_ptr<list<t_A>> Nil_() {
        return std::shared_ptr<list<t_A>>(new list<t_A>(Nil{}));
      }

      static std::shared_ptr<list<t_A>>
      Cons_(t_A a0, const std::shared_ptr<list<t_A>> &a1) {
        return std::shared_ptr<list<t_A>>(new list<t_A>(Cons{a0, a1}));
      }

      static std::unique_ptr<list<t_A>> Nil_uptr() {
        return std::unique_ptr<list<t_A>>(new list<t_A>(Nil{}));
      }

      static std::unique_ptr<list<t_A>>
      Cons_uptr(t_A a0, const std::shared_ptr<list<t_A>> &a1) {
        return std::unique_ptr<list<t_A>>(new list<t_A>(Cons{a0, a1}));
      }
    };

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, typename T2,
            MapsTo<T2, T1, std::shared_ptr<list<T1>>, T2> F1>
  static T2 list_rect(const T2 f, F1 &&f0, const std::shared_ptr<list<T1>> &l) {
    return std::visit(
        Overloaded{[&](const typename list<T1>::Nil _args) -> T2 { return f; },
                   [&](const typename list<T1>::Cons _args) -> T2 {
                     T1 y = _args.d_a0;
                     std::shared_ptr<list<T1>> l0 = _args.d_a1;
                     return f0(y, l0, list_rect<T1, T2>(f, f0, l0));
                   }},
        l->v());
  }

  template <typename T1, typename T2,
            MapsTo<T2, T1, std::shared_ptr<list<T1>>, T2> F1>
  static T2 list_rec(const T2 f, F1 &&f0, const std::shared_ptr<list<T1>> &l) {
    return std::visit(
        Overloaded{[&](const typename list<T1>::Nil _args) -> T2 { return f; },
                   [&](const typename list<T1>::Cons _args) -> T2 {
                     T1 y = _args.d_a0;
                     std::shared_ptr<list<T1>> l0 = _args.d_a1;
                     return f0(y, l0, list_rec<T1, T2>(f, f0, l0));
                   }},
        l->v());
  }

  /// map f l applies f to each element of l, producing a new list.
  template <typename T1, typename T2, MapsTo<T2, T1> F0>
  static std::shared_ptr<list<T2>> map(F0 &&f,
                                       const std::shared_ptr<list<T1>> &l) {
    return std::visit(
        Overloaded{
            [](const typename list<T1>::Nil _args)
                -> std::shared_ptr<list<T2>> { return list<T2>::ctor::Nil_(); },
            [&](const typename list<T1>::Cons _args)
                -> std::shared_ptr<list<T2>> {
              T1 x = _args.d_a0;
              std::shared_ptr<list<T1>> xs = _args.d_a1;
              return list<T2>::ctor::Cons_(f(x), map<T1, T2>(f, std::move(xs)));
            }},
        l->v());
  }

  /// foldr f z l folds l from the right using f with initial
  /// accumulator z.
  template <typename T1, typename T2, MapsTo<T2, T1, T2> F0>
  static T2 foldr(F0 &&f, const T2 z, const std::shared_ptr<list<T1>> &l) {
    return std::visit(
        Overloaded{[&](const typename list<T1>::Nil _args) -> T2 { return z; },
                   [&](const typename list<T1>::Cons _args) -> T2 {
                     T1 x = _args.d_a0;
                     std::shared_ptr<list<T1>> xs = _args.d_a1;
                     return f(x, foldr<T1, T2>(f, z, std::move(xs)));
                   }},
        l->v());
  }

  /// foldl f z l folds l from the left using f with initial
  /// accumulator z. This is tail-recursive.
  template <typename T1, typename T2, MapsTo<T2, T2, T1> F0>
  static T2 foldl(F0 &&f, const T2 z, const std::shared_ptr<list<T1>> &l) {
    return std::visit(
        Overloaded{[&](const typename list<T1>::Nil _args) -> T2 { return z; },
                   [&](const typename list<T1>::Cons _args) -> T2 {
                     T1 x = _args.d_a0;
                     std::shared_ptr<list<T1>> xs = _args.d_a1;
                     return foldl<T1, T2>(f, f(z, x), std::move(xs));
                   }},
        l->v());
  }

  /// compose g f returns the composition of g after f.
  template <typename T1, typename T2, typename T3, typename F0, typename F1>
  static T3 compose(F0 &&g, F1 &&f, const T1 x) {
    return g(f(x));
  }

  /// iterate n f x applies f to x a total of n times.
  template <typename T1, MapsTo<T1, T1> F1>
  static T1 iterate(const unsigned int n, F1 &&f, const T1 x) {
    if (n <= 0) {
      return x;
    } else {
      unsigned int m = n - 1;
      return f(iterate<T1>(m, f, x));
    }
  }

  /// adder n returns a function that adds n to its argument.
  __attribute__((pure)) static unsigned int adder(const unsigned int _x0,
                                                  const unsigned int _x1);

  /// twice f returns a function that applies f two times.
  template <typename T1, MapsTo<T1, T1> F0>
  static T1 twice(F0 &&f, const T1 x) {
    return f(f(x));
  }

  /// pipe x f applies f to x, simulating a pipeline operator.
  template <typename T1, typename T2, MapsTo<T2, T1> F1>
  static T2 pipe(const T1 x, F1 &&f) {
    return f(x);
  }

  static inline const std::shared_ptr<list<unsigned int>> test_list =
      list<unsigned int>::ctor::Cons_(
          1u,
          list<unsigned int>::ctor::Cons_(
              2u, list<unsigned int>::ctor::Cons_(
                      3u, list<unsigned int>::ctor::Cons_(
                              4u, list<unsigned int>::ctor::Cons_(
                                      5u, list<unsigned int>::ctor::Nil_())))));
  static inline const unsigned int test_map = foldr<unsigned int, unsigned int>(
      [](unsigned int _x0, unsigned int _x1) -> unsigned int {
        return (_x0 + _x1);
      },
      0u,
      map<unsigned int, unsigned int>(
          [](unsigned int _x0) -> unsigned int { return (1u + _x0); },
          test_list));
  static inline const unsigned int test_foldr =
      foldr<unsigned int, unsigned int>(
          [](unsigned int _x0, unsigned int _x1) -> unsigned int {
            return (_x0 + _x1);
          },
          0u, test_list);
  static inline const unsigned int test_foldl =
      foldl<unsigned int, unsigned int>(
          [](unsigned int _x0, unsigned int _x1) -> unsigned int {
            return (_x0 + _x1);
          },
          0u, test_list);
  static inline const unsigned int test_compose =
      compose<unsigned int, unsigned int, unsigned int>(
          [](unsigned int _x0) -> unsigned int { return (2u * _x0); },
          [](unsigned int _x0) -> unsigned int { return (1u + _x0); }, 3u);
  static inline const unsigned int test_iterate = iterate<unsigned int>(
      3u, [](unsigned int _x0) -> unsigned int { return (2u + _x0); }, 0u);
  static inline const unsigned int test_adder = adder(5u, 3u);
  static inline const unsigned int test_twice = twice<unsigned int>(
      [](unsigned int _x0) -> unsigned int { return (1u + _x0); }, 5u);
  static inline const unsigned int test_pipe = pipe<unsigned int, unsigned int>(
      5u, [](unsigned int _x0) -> unsigned int { return adder(3u, _x0); });
};

#endif // INCLUDED_HIGHER_ORDER
