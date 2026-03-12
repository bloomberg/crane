#ifndef INCLUDED_TYPE_APP
#define INCLUDED_TYPE_APP

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

template <typename M>
concept Monoid = requires {
  typename M::T;
  requires(
      requires {
        { M::empty } -> std::convertible_to<typename M::T>;
      } ||
      requires {
        { M::empty() } -> std::convertible_to<typename M::T>;
      });
  {
    M::append(std::declval<typename M::T>(), std::declval<typename M::T>())
  } -> std::same_as<typename M::T>;
};

struct TypeApp {
  template <typename T1> static T1 id(const T1 x) { return x; }

  static inline const unsigned int id_int = id<unsigned int>(42u);
  static inline const bool id_bool = id<bool>(true);

  template <typename T1, typename T2, typename T3, typename F0, typename F1>
  static T3 compose(F0 &&g, F1 &&f, const T1 x) {
    return g(f(x));
  }

  template <typename T1> static T1 nested_poly(const T1 x) {
    return id<T1>(id<T1>(id<T1>(x)));
  }

  template <typename A> struct list {
    // TYPES
    struct nil {};

    struct cons {
      A _a0;
      std::shared_ptr<list<A>> _a1;
    };

    using variant_t = std::variant<nil, cons>;

  private:
    // DATA
    variant_t v_;

    // CREATORS
    explicit list(nil _v) : v_(std::move(_v)) {}

    explicit list(cons _v) : v_(std::move(_v)) {}

  public:
    // TYPES
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

    // MANIPULATORS
    variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
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

  static inline const std::shared_ptr<list<unsigned int>> test_map =
      map<unsigned int, unsigned int>(
          [](unsigned int x) { return (x + 1u); },
          list<unsigned int>::ctor::cons_(
              1u, list<unsigned int>::ctor::cons_(
                      2u, list<unsigned int>::ctor::cons_(
                              3u, list<unsigned int>::ctor::nil_()))));
  static std::shared_ptr<list<unsigned int>>
  map_succ(const std::shared_ptr<list<unsigned int>> &_x0);
  static inline const std::shared_ptr<list<unsigned int>> test_map_succ =
      map_succ(list<unsigned int>::ctor::cons_(
          5u, list<unsigned int>::ctor::cons_(
                  6u, list<unsigned int>::ctor::nil_())));

  template <typename T1, MapsTo<T1, T1> F0>
  static T1 twice(F0 &&f, const T1 x) {
    return f(f(x));
  }

  static inline const unsigned int test_twice =
      twice<unsigned int>([](unsigned int x) { return (x + 1u); }, 10u);

  struct NatMonoid {
    using T = unsigned int;
    static inline const unsigned int empty = 0u;
    static unsigned int append(const unsigned int _x0, const unsigned int _x1);
  };

  template <Monoid M> struct UseMonoid {
    static const typename M::T &combine_empty() {
      static const typename M::T v = M::append(M::empty, M::empty);
      return v;
    }

    static typename M::T triple(const typename M::T x) {
      return M::append(x, M::append(x, x));
    }
  };

  using NatMonoidUser = UseMonoid<NatMonoid>;
  static inline const NatMonoid::T monoid_test = NatMonoidUser::combine_empty();
};

#endif // INCLUDED_TYPE_APP
