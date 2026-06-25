#ifndef INCLUDED_COIND_GUARD
#define INCLUDED_COIND_GUARD

#include "lazy.h"
#include <any>
#include <functional>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

template <typename A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    A a;
    std::shared_ptr<List<A>> l;
  };

  using variant_t = std::variant<Nil, Cons>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  List() {}

  explicit List(Nil _v) : v_(_v) {}

  explicit List(Cons _v) : v_(std::move(_v)) {}

  template <typename _U> explicit List(const List<_U> &_other) {
    if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
      this->v_ = Nil{};
    } else {
      const auto &[a, l] = std::get<typename List<_U>::Cons>(_other.v());
      this->v_ = Cons{
          [&]() -> A {
            if constexpr (std::is_same_v<_U, std::any>) {
              if (a.type() == typeid(A))
                return std::any_cast<A>(a);
              if constexpr (requires {
                              typename A::first_type;
                              typename A::second_type;
                            }) {
                const auto &[_k, _v] =
                    std::any_cast<std::pair<std::any, std::any>>(a);
                return A{[&]() -> typename A::first_type {
                           if constexpr (std::is_same_v<typename A::first_type,
                                                        std::any>)
                             return _k;
                           else
                             return std::any_cast<typename A::first_type>(_k);
                         }(),
                         [&]() -> typename A::second_type {
                           if constexpr (std::is_same_v<typename A::second_type,
                                                        std::any>)
                             return _v;
                           else
                             return std::any_cast<typename A::second_type>(_v);
                         }()};
              }
              return std::any_cast<A>(a);
            } else
              return A(a);
          }(),
          l ? std::make_shared<List<A>>(*l) : nullptr};
    }
  }

  static List<A> nil() { return List(Nil{}); }

  static List<A> cons(A a, List<A> l) {
    return List(Cons{std::move(a), std::make_shared<List<A>>(std::move(l))});
  }

  // MANIPULATORS
  ~List() {
    std::vector<std::shared_ptr<List<A>>> _stack = {};
    auto _drain = [&](variant_t &_v) {
      if (auto *_alt = std::get_if<Cons>(&_v)) {
        if (_alt->l) {
          _stack.push_back(std::move(_alt->l));
        }
      }
    };
    _drain(v_mut());
    while (!_stack.empty()) {
      auto _cur = std::move(_stack.back());
      _stack.pop_back();
      if (_cur.use_count() == 1) {
        _drain(_cur->v_mut());
      }
    }
  }

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

struct CoindGuard {
  template <typename A> struct Stream {
    // TYPES
    struct Cons {
      A a0;
      std::shared_ptr<Stream<A>> a1;
    };

    using variant_t = std::variant<Cons>;

  private:
    // DATA
    crane::lazy<variant_t> lazy_v_;

  public:
    // CREATORS
    explicit Stream(Cons _v)
        : lazy_v_(crane::lazy<variant_t>(variant_t(std::move(_v)))) {}

    explicit Stream(std::function<variant_t()> _thunk)
        : lazy_v_(crane::lazy<variant_t>(std::move(_thunk))) {}

    static Stream<A> cons(A a0, const Stream<A> &a1) {
      return Stream(Cons{std::move(a0), std::make_shared<Stream<A>>(a1)});
    }

    static Stream<A> lazy_(std::function<Stream<A>()> thunk) {
      return Stream<A>(std::function<variant_t()>([=]() mutable -> variant_t {
        Stream<A> _tmp = thunk();
        return _tmp.v();
      }));
    }

    // ACCESSORS
    const variant_t &v() const { return lazy_v_.force(); }
  };

  template <typename T1> static T1 hd(Stream<T1> s) {
    const auto &[a0, a1] = std::get<typename Stream<T1>::Cons>(s.v());
    return a0;
  }

  template <typename T1> static Stream<T1> tl(Stream<T1> s) {
    const auto &[a0, a1] = std::get<typename Stream<T1>::Cons>(s.v());
    return Stream<T1>::lazy_([=]() mutable -> Stream<T1> { return *a1; });
  }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, T1 &>
  static Stream<T1> iterate(F0 &&f, T1 x) {
    return Stream<T1>::lazy_([=]() mutable -> Stream<T1> {
      return Stream<T1>::cons(x, iterate<T1>(f, f(x)));
    });
  }

  template <typename T1, typename T2, typename T3, typename F0>
    requires std::is_invocable_r_v<T3, F0 &, T1 &, T2 &>
  static Stream<T3> zipWith(F0 &&f, Stream<T1> s1, Stream<T2> s2) {
    return Stream<T3>::lazy_([=]() mutable -> Stream<T3> {
      return Stream<T3>::cons(f(hd<T1>(s1), hd<T2>(s2)),
                              zipWith<T1, T2, T3>(f, tl<T1>(s1), tl<T2>(s2)));
    });
  }

  template <typename T1, typename T2, typename F0>
    requires std::is_invocable_r_v<T2, F0 &, T1 &>
  static Stream<T2> smap(F0 &&f, Stream<T1> s) {
    return Stream<T2>::lazy_([=]() mutable -> Stream<T2> {
      return Stream<T2>::cons(f(hd<T1>(s)), smap<T1, T2>(f, tl<T1>(s)));
    });
  }

  template <typename T1, typename T2, typename F0>
    requires std::is_invocable_r_v<std::pair<T1, T2>, F0 &, T2 &>
  static Stream<T1> unfold(F0 &&f, const T2 &seed) {
    auto [a, s_] = f(seed);
    return Stream<T1>::lazy_([=]() mutable -> Stream<T1> {
      return Stream<T1>::cons(a, unfold<T1, T2>(f, s_));
    });
  }

  template <typename T1> static List<T1> take(uint64_t n, Stream<T1> s) {
    if (n <= 0) {
      return List<T1>::nil();
    } else {
      uint64_t n_ = n - 1;
      return List<T1>::cons(hd<T1>(s), take<T1>(n_, tl<T1>(s)));
    }
  }

  static inline const Stream<uint64_t> nats =
      iterate<uint64_t>([](uint64_t x) { return (x + 1); }, UINT64_C(0));
  static inline const Stream<uint64_t> evens = smap<uint64_t, uint64_t>(
      [](uint64_t n) { return (n * UINT64_C(2)); }, nats);
  static inline const Stream<uint64_t> fibs =
      unfold<uint64_t, std::pair<uint64_t, uint64_t>>(
          [](std::pair<uint64_t, uint64_t> pat) {
            const auto &[a, b] = pat;
            return std::make_pair(a, std::make_pair(b, (a + b)));
          },
          std::make_pair(UINT64_C(0), UINT64_C(1)));
  static inline const Stream<uint64_t> sum_stream =
      zipWith<uint64_t, uint64_t, uint64_t>(
          [](uint64_t _x0, uint64_t _x1) -> uint64_t { return (_x0 + _x1); },
          nats, evens);
  static inline const List<uint64_t> test_nats_5 =
      take<uint64_t>(UINT64_C(5), nats);
  static inline const List<uint64_t> test_evens_5 =
      take<uint64_t>(UINT64_C(5), evens);
  static inline const List<uint64_t> test_fibs_8 =
      take<uint64_t>(UINT64_C(8), fibs);
  static inline const List<uint64_t> test_sum_5 =
      take<uint64_t>(UINT64_C(5), sum_stream);
  static inline const uint64_t test_iterate_hd = hd<uint64_t>(nats);
};

#endif // INCLUDED_COIND_GUARD
