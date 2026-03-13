#ifndef INCLUDED_COIND_GUARD
#define INCLUDED_COIND_GUARD

#include "lazy.h"
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

template <typename t_A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    t_A d_a0;
    std::shared_ptr<List<t_A>> d_a1;
  };

  using variant_t = std::variant<Nil, Cons>;

private:
  // DATA
  variant_t d_v_;

  // CREATORS
  explicit List(Nil _v) : d_v_(std::move(_v)) {}

  explicit List(Cons _v) : d_v_(std::move(_v)) {}

public:
  // TYPES
  struct ctor {
    ctor() = delete;

    static std::shared_ptr<List<t_A>> Nil_() {
      return std::shared_ptr<List<t_A>>(new List<t_A>(Nil{}));
    }

    static std::shared_ptr<List<t_A>>
    Cons_(t_A a0, const std::shared_ptr<List<t_A>> &a1) {
      return std::shared_ptr<List<t_A>>(new List<t_A>(Cons{a0, a1}));
    }

    static std::unique_ptr<List<t_A>> Nil_uptr() {
      return std::unique_ptr<List<t_A>>(new List<t_A>(Nil{}));
    }

    static std::unique_ptr<List<t_A>>
    Cons_uptr(t_A a0, const std::shared_ptr<List<t_A>> &a1) {
      return std::unique_ptr<List<t_A>>(new List<t_A>(Cons{a0, a1}));
    }
  };

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }
};

struct CoindGuard {
  template <typename t_A> struct Stream {
    // TYPES
    struct Cons {
      t_A d_a0;
      std::shared_ptr<Stream<t_A>> d_a1;
    };

    using variant_t = std::variant<Cons>;

  private:
    // DATA
    crane::lazy<variant_t> d_lazyV_;

    // CREATORS
    explicit Stream(Cons _v)
        : d_lazyV_(crane::lazy<variant_t>(variant_t(std::move(_v)))) {}

    explicit Stream(std::function<variant_t()> _thunk)
        : d_lazyV_(crane::lazy<variant_t>(std::move(_thunk))) {}

  public:
    // TYPES
    struct ctor {
      ctor() = delete;

      static std::shared_ptr<Stream<t_A>>
      Cons_(t_A a0, const std::shared_ptr<Stream<t_A>> &a1) {
        return std::shared_ptr<Stream<t_A>>(new Stream<t_A>(Cons{a0, a1}));
      }

      static std::unique_ptr<Stream<t_A>>
      Cons_uptr(t_A a0, const std::shared_ptr<Stream<t_A>> &a1) {
        return std::unique_ptr<Stream<t_A>>(new Stream<t_A>(Cons{a0, a1}));
      }

      static std::shared_ptr<Stream<t_A>>
      lazy_(std::function<std::shared_ptr<Stream<t_A>>()> thunk) {
        return std::shared_ptr<Stream<t_A>>(new Stream<t_A>(
            std::function<variant_t()>([=](void) mutable -> variant_t {
              std::shared_ptr<Stream<t_A>> _tmp = thunk();
              return _tmp->v();
            })));
      }
    };

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const {
      return d_lazyV_.force();
    }
  };

  template <typename T1> static T1 hd(const std::shared_ptr<Stream<T1>> &s) {
    return std::visit(
        Overloaded{[](const typename Stream<T1>::Cons _args) -> T1 {
          T1 x = _args.d_a0;
          return x;
        }},
        s->v());
  }

  template <typename T1>
  static std::shared_ptr<Stream<T1>> tl(const std::shared_ptr<Stream<T1>> &s) {
    return Stream<T1>::ctor::lazy_(
        [=](void) mutable -> std::shared_ptr<Stream<T1>> {
          return std::visit(Overloaded{[](const typename Stream<T1>::Cons _args)
                                           -> std::shared_ptr<Stream<T1>> {
                              std::shared_ptr<Stream<T1>> t = _args.d_a1;
                              return t;
                            }},
                            s->v());
        });
  }

  template <typename T1, MapsTo<T1, T1> F0>
  static std::shared_ptr<Stream<T1>> iterate(F0 &&f, const T1 x) {
    return Stream<T1>::ctor::lazy_(
        [=](void) mutable -> std::shared_ptr<Stream<T1>> {
          return Stream<T1>::ctor::Cons_(x, iterate<T1>(f, f(x)));
        });
  }

  template <typename T1, typename T2, typename T3, MapsTo<T3, T1, T2> F0>
  static std::shared_ptr<Stream<T3>> zipWith(F0 &&f,
                                             std::shared_ptr<Stream<T1>> s1,
                                             std::shared_ptr<Stream<T2>> s2) {
    return Stream<T3>::ctor::lazy_(
        [=](void) mutable -> std::shared_ptr<Stream<T3>> {
          return Stream<T3>::ctor::Cons_(
              f(hd<T1>(s1), hd<T2>(s2)),
              zipWith<T1, T2, T3>(f, tl<T1>(s1), tl<T2>(s2)));
        });
  }

  template <typename T1, typename T2, MapsTo<T2, T1> F0>
  static std::shared_ptr<Stream<T2>> smap(F0 &&f,
                                          std::shared_ptr<Stream<T1>> s) {
    return Stream<T2>::ctor::lazy_(
        [=](void) mutable -> std::shared_ptr<Stream<T2>> {
          return Stream<T2>::ctor::Cons_(f(hd<T1>(s)),
                                         smap<T1, T2>(f, tl<T1>(s)));
        });
  }

  template <typename T1, typename T2, MapsTo<std::pair<T1, T2>, T2> F0>
  static std::shared_ptr<Stream<T1>> unfold(F0 &&f, const T2 seed) {
    T1 a = f(seed).first;
    T2 s_ = f(seed).second;
    return Stream<T1>::ctor::lazy_(
        [=](void) mutable -> std::shared_ptr<Stream<T1>> {
          return Stream<T1>::ctor::Cons_(a, unfold<T1, T2>(f, s_));
        });
  }

  template <typename T1>
  static std::shared_ptr<List<T1>> take(const unsigned int n,
                                        std::shared_ptr<Stream<T1>> s) {
    if (n <= 0) {
      return List<T1>::ctor::Nil_();
    } else {
      unsigned int n_ = n - 1;
      return List<T1>::ctor::Cons_(hd<T1>(s), take<T1>(n_, tl<T1>(s)));
    }
  }

  static inline const std::shared_ptr<Stream<unsigned int>> nats =
      iterate<unsigned int>([](unsigned int x) { return (x + 1); }, 0u);
  static inline const std::shared_ptr<Stream<unsigned int>> evens =
      smap<unsigned int, unsigned int>([](unsigned int n) { return (n * 2u); },
                                       nats);
  static inline const std::shared_ptr<Stream<unsigned int>> fibs =
      unfold<unsigned int, std::pair<unsigned int, unsigned int>>(
          [](std::pair<unsigned int, unsigned int> pat) {
            unsigned int a = pat.first;
            unsigned int b = pat.second;
            return std::make_pair(a, std::make_pair(b, (a + b)));
          },
          std::make_pair(0u, 1u));
  static inline const std::shared_ptr<Stream<unsigned int>> sum_stream =
      zipWith<unsigned int, unsigned int, unsigned int>(
          [](unsigned int _x0, unsigned int _x1) -> unsigned int {
            return (_x0 + _x1);
          },
          nats, evens);
  static inline const std::shared_ptr<List<unsigned int>> test_nats_5 =
      take<unsigned int>(5u, nats);
  static inline const std::shared_ptr<List<unsigned int>> test_evens_5 =
      take<unsigned int>(5u, evens);
  static inline const std::shared_ptr<List<unsigned int>> test_fibs_8 =
      take<unsigned int>(8u, fibs);
  static inline const std::shared_ptr<List<unsigned int>> test_sum_5 =
      take<unsigned int>(5u, sum_stream);
  static inline const unsigned int test_iterate_hd = hd<unsigned int>(nats);
};

#endif // INCLUDED_COIND_GUARD
