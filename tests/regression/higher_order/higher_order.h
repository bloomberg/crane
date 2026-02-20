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

struct HigherOrder {
  template <typename A> struct list {
  public:
    struct nil {};
    struct cons {
      A _a0;
      std::shared_ptr<list<A>> _a1;
    };
    using variant_t = std::variant<nil, cons>;

  private:
    variant_t v_;
    explicit list(nil _v) : v_(std::move(_v)) {}
    explicit list(cons _v) : v_(std::move(_v)) {}

  public:
    struct ctor {
      ctor() = delete;
      static std::shared_ptr<list<A>> nil_() {
        return std::shared_ptr<list<A>>(new list<A>(nil{}));
      }
      static std::shared_ptr<list<A>>
      cons_(A a0, const std::shared_ptr<list<A>> &a1) {
        return std::shared_ptr<list<A>>(new list<A>(cons{a0, a1}));
      }
      static std::unique_ptr<list<A>> nil_uptr() {
        return std::unique_ptr<list<A>>(new list<A>(nil{}));
      }
      static std::unique_ptr<list<A>>
      cons_uptr(A a0, const std::shared_ptr<list<A>> &a1) {
        return std::unique_ptr<list<A>>(new list<A>(cons{a0, a1}));
      }
    };
    const variant_t &v() const { return v_; }
    variant_t &v_mut() { return v_; }
  };

  template <typename T1, typename T2,
            MapsTo<T2, T1, std::shared_ptr<list<T1>>, T2> F1>
  static T2 list_rect(const T2 f, F1 &&f0, const std::shared_ptr<list<T1>> &l) {
    return std::visit(
        Overloaded{[&](const typename list<T1>::nil _args) -> T2 { return f; },
                   [&](const typename list<T1>::cons _args) -> T2 {
                     T1 y = _args._a0;
                     std::shared_ptr<list<T1>> l0 = _args._a1;
                     return f0(y, l0, list_rect<T1, T2>(f, f0, l0));
                   }},
        l->v());
  }

  template <typename T1, typename T2,
            MapsTo<T2, T1, std::shared_ptr<list<T1>>, T2> F1>
  static T2 list_rec(const T2 f, F1 &&f0, const std::shared_ptr<list<T1>> &l) {
    return std::visit(
        Overloaded{[&](const typename list<T1>::nil _args) -> T2 { return f; },
                   [&](const typename list<T1>::cons _args) -> T2 {
                     T1 y = _args._a0;
                     std::shared_ptr<list<T1>> l0 = _args._a1;
                     return f0(y, l0, list_rec<T1, T2>(f, f0, l0));
                   }},
        l->v());
  }

  template <typename T1, typename T2, MapsTo<T2, T1> F0>
  static std::shared_ptr<list<T2>> map(F0 &&f,
                                       const std::shared_ptr<list<T1>> &l) {
    return std::visit(
        Overloaded{
            [](const typename list<T1>::nil _args)
                -> std::shared_ptr<list<T2>> { return list<T2>::ctor::nil_(); },
            [&](const typename list<T1>::cons _args)
                -> std::shared_ptr<list<T2>> {
              T1 x = _args._a0;
              std::shared_ptr<list<T1>> xs = _args._a1;
              return list<T2>::ctor::cons_(f(x), map<T1, T2>(f, std::move(xs)));
            }},
        l->v());
  }

  template <typename T1, typename T2, MapsTo<T2, T1, T2> F0>
  static T2 foldr(F0 &&f, const T2 z, const std::shared_ptr<list<T1>> &l) {
    return std::visit(
        Overloaded{[&](const typename list<T1>::nil _args) -> T2 { return z; },
                   [&](const typename list<T1>::cons _args) -> T2 {
                     T1 x = _args._a0;
                     std::shared_ptr<list<T1>> xs = _args._a1;
                     return f(x, foldr<T1, T2>(f, z, std::move(xs)));
                   }},
        l->v());
  }

  template <typename T1, typename T2, MapsTo<T2, T2, T1> F0>
  static T2 foldl(F0 &&f, const T2 z, const std::shared_ptr<list<T1>> &l) {
    return std::visit(
        Overloaded{[&](const typename list<T1>::nil _args) -> T2 { return z; },
                   [&](const typename list<T1>::cons _args) -> T2 {
                     T1 x = _args._a0;
                     std::shared_ptr<list<T1>> xs = _args._a1;
                     return foldl<T1, T2>(f, f(z, x), std::move(xs));
                   }},
        l->v());
  }

  template <typename T1, typename T2, typename T3, MapsTo<T3, T2> F0,
            MapsTo<T2, T1> F1>
  static T3 compose(F0 &&g, F1 &&f, const T1 x) {
    return g(f(x));
  }

  template <typename T1, MapsTo<T1, T1> F1>
  static T1 iterate(const unsigned int n, F1 &&f, const T1 x) {
    if (n <= 0) {
      return x;
    } else {
      unsigned int m = n - 1;
      return f(iterate<T1>(m, f, x));
    }
  }

  static unsigned int adder(const unsigned int, const unsigned int);

  template <typename T1, MapsTo<T1, T1> F0>
  static T1 twice(F0 &&f, const T1 x) {
    return f(f(x));
  }

  template <typename T1, typename T2, MapsTo<T2, T1> F1>
  static T2 pipe(const T1 x, F1 &&f) {
    return f(x);
  }

  static inline const std::shared_ptr<list<unsigned int>> test_list =
      list<unsigned int>::ctor::cons_(
          1u,
          list<unsigned int>::ctor::cons_(
              2u, list<unsigned int>::ctor::cons_(
                      3u, list<unsigned int>::ctor::cons_(
                              4u, list<unsigned int>::ctor::cons_(
                                      5u, list<unsigned int>::ctor::nil_())))));

  static inline const unsigned int test_map = foldr<unsigned int, unsigned int>(
      [](const unsigned int _x0, const unsigned int _x1) {
        return (_x0 + _x1);
      },
      0u,
      map<unsigned int, unsigned int>(
          [](const unsigned int _x0) { return (1u + _x0); }, test_list));

  static inline const unsigned int test_foldr =
      foldr<unsigned int, unsigned int>(
          [](const unsigned int _x0, const unsigned int _x1) {
            return (_x0 + _x1);
          },
          0u, test_list);

  static inline const unsigned int test_foldl =
      foldl<unsigned int, unsigned int>(
          [](const unsigned int _x0, const unsigned int _x1) {
            return (_x0 + _x1);
          },
          0u, test_list);

  static inline const unsigned int test_compose =
      compose<unsigned int, unsigned int, unsigned int>(
          [](const unsigned int _x0) { return (2u * _x0); },
          [](const unsigned int _x0) { return (1u + _x0); }, 3u);

  static inline const unsigned int test_iterate = iterate<unsigned int>(
      3u, [](const unsigned int _x0) { return (2u + _x0); }, 0u);

  static inline const unsigned int test_adder = adder(5u, 3u);

  static inline const unsigned int test_twice = twice<unsigned int>(
      [](const unsigned int _x0) { return (1u + _x0); }, 5u);

  static inline const unsigned int test_pipe = pipe<unsigned int, unsigned int>(
      5u, [](const unsigned int _x0) { return adder(3u, _x0); });
};
