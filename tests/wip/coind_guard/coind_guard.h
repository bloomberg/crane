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

template <typename A> struct List {
public:
  struct nil {};
  struct cons {
    A _a0;
    std::shared_ptr<List<A>> _a1;
  };
  using variant_t = std::variant<nil, cons>;

private:
  variant_t v_;
  explicit List(nil _v) : v_(std::move(_v)) {}
  explicit List(cons _v) : v_(std::move(_v)) {}

public:
  struct ctor {
    ctor() = delete;
    static std::shared_ptr<List<A>> nil_() {
      return std::shared_ptr<List<A>>(new List<A>(nil{}));
    }
    static std::shared_ptr<List<A>> cons_(A a0,
                                          const std::shared_ptr<List<A>> &a1) {
      return std::shared_ptr<List<A>>(new List<A>(cons{a0, a1}));
    }
    static std::unique_ptr<List<A>> nil_uptr() {
      return std::unique_ptr<List<A>>(new List<A>(nil{}));
    }
    static std::unique_ptr<List<A>>
    cons_uptr(A a0, const std::shared_ptr<List<A>> &a1) {
      return std::unique_ptr<List<A>>(new List<A>(cons{a0, a1}));
    }
  };
  const variant_t &v() const { return v_; }
  variant_t &v_mut() { return v_; }
};

struct CoindGuard {
  template <typename A> struct Stream {
  public:
    struct Cons {
      A _a0;
      std::shared_ptr<Stream<A>> _a1;
    };
    using variant_t = std::variant<Cons>;

  private:
    crane::lazy<variant_t> lazy_v_;
    explicit Stream(Cons _v)
        : lazy_v_(crane::lazy<variant_t>(variant_t(std::move(_v)))) {}
    explicit Stream(std::function<variant_t()> _thunk)
        : lazy_v_(crane::lazy<variant_t>(std::move(_thunk))) {}

  public:
    struct ctor {
      ctor() = delete;
      static std::shared_ptr<Stream<A>>
      Cons_(A a0, const std::shared_ptr<Stream<A>> &a1) {
        return std::shared_ptr<Stream<A>>(new Stream<A>(Cons{a0, a1}));
      }
      static std::unique_ptr<Stream<A>>
      Cons_uptr(A a0, const std::shared_ptr<Stream<A>> &a1) {
        return std::unique_ptr<Stream<A>>(new Stream<A>(Cons{a0, a1}));
      }
      static std::shared_ptr<Stream<A>>
      lazy_(std::function<std::shared_ptr<Stream<A>>()> thunk) {
        return std::shared_ptr<Stream<A>>(
            new Stream<A>(std::function<variant_t()>([=](void) -> variant_t {
              std::shared_ptr<Stream<A>> _tmp = thunk();
              return std::move(const_cast<variant_t &>(_tmp->v()));
            })));
      }
    };
    const variant_t &v() const { return lazy_v_.force(); }
  };

  template <typename T1> static T1 hd(const std::shared_ptr<Stream<T1>> &s) {
    return std::visit(
        Overloaded{[](const typename Stream<T1>::Cons _args) -> T1 {
          T1 x = _args._a0;
          return x;
        }},
        s->v());
  }

  template <typename T1>
  static std::shared_ptr<Stream<T1>> tl(const std::shared_ptr<Stream<T1>> &s) {
    return Stream<T1>::ctor::lazy_([=](void) -> std::shared_ptr<Stream<T1>> {
      return std::visit(Overloaded{[](const typename Stream<T1>::Cons _args)
                                       -> std::shared_ptr<Stream<T1>> {
                          std::shared_ptr<Stream<T1>> t = _args._a1;
                          return t;
                        }},
                        s->v());
    });
  }

  template <typename T1, MapsTo<T1, T1> F0>
  static std::shared_ptr<Stream<T1>> iterate(F0 &&f, const T1 x) {
    return Stream<T1>::ctor::lazy_([=](void) -> std::shared_ptr<Stream<T1>> {
      return Stream<T1>::ctor::Cons_(x, iterate<T1>(f, f(x)));
    });
  }

  template <typename T1, typename T2, typename T3, MapsTo<T3, T1, T2> F0>
  static std::shared_ptr<Stream<T3>> zipWith(F0 &&f,
                                             std::shared_ptr<Stream<T1>> s1,
                                             std::shared_ptr<Stream<T2>> s2) {
    return Stream<T3>::ctor::lazy_([=](void) -> std::shared_ptr<Stream<T3>> {
      return Stream<T3>::ctor::Cons_(
          f(hd<T1>(s1), hd<T2>(s2)),
          zipWith<T1, T2, T3>(f, tl<T1>(s1), tl<T2>(s2)));
    });
  }

  template <typename T1, typename T2, MapsTo<T2, T1> F0>
  static std::shared_ptr<Stream<T2>> smap(F0 &&f,
                                          std::shared_ptr<Stream<T1>> s) {
    return Stream<T2>::ctor::lazy_([=](void) -> std::shared_ptr<Stream<T2>> {
      return Stream<T2>::ctor::Cons_(f(hd<T1>(s)), smap<T1, T2>(f, tl<T1>(s)));
    });
  }

  template <typename T1, typename T2, MapsTo<std::pair<T1, T2>, T2> F0>
  static std::shared_ptr<Stream<T1>> unfold(F0 &&f, const T2 seed) {
    T1 a = f(seed).first;
    T2 s_ = f(seed).second;
    return Stream<T1>::ctor::lazy_([=](void) -> std::shared_ptr<Stream<T1>> {
      return Stream<T1>::ctor::Cons_(a, unfold<T1, T2>(f, s_));
    });
  }

  template <typename T1>
  static std::shared_ptr<List<T1>> take(const unsigned int n,
                                        std::shared_ptr<Stream<T1>> s) {
    if (n <= 0) {
      return List<T1>::ctor::nil_();
    } else {
      unsigned int n_ = n - 1;
      return List<T1>::ctor::cons_(hd<T1>(s), take<T1>(n_, tl<T1>(s)));
    }
  }

  static inline const std::shared_ptr<Stream<unsigned int>> nats =
      iterate<unsigned int>([](unsigned int x) { return (x + 1); }, 0);

  static inline const std::shared_ptr<Stream<unsigned int>> evens =
      smap<unsigned int, unsigned int>(
          [](unsigned int n) { return (n * ((0 + 1) + 1)); }, nats);

  static inline const std::shared_ptr<Stream<unsigned int>> fibs =
      unfold<unsigned int, std::pair<unsigned int, unsigned int>>(
          [](std::pair<unsigned int, unsigned int> pat) {
            unsigned int a = pat.first;
            unsigned int b = pat.second;
            return std::make_pair(a, std::make_pair(b, (a + b)));
          },
          std::make_pair(0, (0 + 1)));

  static inline const std::shared_ptr<Stream<unsigned int>> sum_stream =
      zipWith<unsigned int, unsigned int, unsigned int>(
          [](const unsigned int _x0, const unsigned int _x1) {
            return (_x0 + _x1);
          },
          nats, evens);

  static inline const std::shared_ptr<List<unsigned int>> test_nats_5 =
      take<unsigned int>((((((0 + 1) + 1) + 1) + 1) + 1), nats);

  static inline const std::shared_ptr<List<unsigned int>> test_evens_5 =
      take<unsigned int>((((((0 + 1) + 1) + 1) + 1) + 1), evens);

  static inline const std::shared_ptr<List<unsigned int>> test_fibs_8 =
      take<unsigned int>(((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1),
                         fibs);

  static inline const std::shared_ptr<List<unsigned int>> test_sum_5 =
      take<unsigned int>((((((0 + 1) + 1) + 1) + 1) + 1), sum_stream);

  static inline const unsigned int test_iterate_hd = hd<unsigned int>(nats);
};
