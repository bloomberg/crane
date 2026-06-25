#ifndef INCLUDED_LOOPIFY_COIND_STREAM
#define INCLUDED_LOOPIFY_COIND_STREAM

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

struct LoopifyCoindStream {
  template <typename A> struct stream {
    // TYPES
    struct Scons {
      A a0;
      std::shared_ptr<stream<A>> a1;
    };

    using variant_t = std::variant<Scons>;

  private:
    // DATA
    crane::lazy<variant_t> lazy_v_;

  public:
    // CREATORS
    explicit stream(Scons _v)
        : lazy_v_(crane::lazy<variant_t>(variant_t(std::move(_v)))) {}

    explicit stream(std::function<variant_t()> _thunk)
        : lazy_v_(crane::lazy<variant_t>(std::move(_thunk))) {}

    static stream<A> scons(A a0, const stream<A> &a1) {
      return stream(Scons{std::move(a0), std::make_shared<stream<A>>(a1)});
    }

    static stream<A> lazy_(std::function<stream<A>()> thunk) {
      return stream<A>(std::function<variant_t()>([=]() mutable -> variant_t {
        stream<A> _tmp = thunk();
        return _tmp.v();
      }));
    }

    // ACCESSORS
    const variant_t &v() const { return lazy_v_.force(); }
  };

  template <typename T1> static T1 hd(stream<T1> s) {
    const auto &[a0, a1] = std::get<typename stream<T1>::Scons>(s.v());
    return a0;
  }

  template <typename T1> static stream<T1> tl(stream<T1> s) {
    const auto &[a0, a1] = std::get<typename stream<T1>::Scons>(s.v());
    return stream<T1>::lazy_([=]() mutable -> stream<T1> { return *a1; });
  }

  template <typename T1>
  static List<T1> take(uint64_t n,
                       stream<T1> s) { /// _Enter: captures varying parameters
                                       /// for each recursive call.

    struct _Enter {
      stream<T1> s;
      uint64_t n;
    };

    /// _Resume_n_: saves [s], resumes after recursive call with _result.
    struct _Resume_n_ {
      std::decay_t<decltype(hd<T1>(std::declval<stream<T1> &>()))> s;
    };

    using _Frame = std::variant<_Enter, _Resume_n_>;
    List<T1> _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{std::move(s), n});
    /// Loopified take: _Enter -> _Resume_n_.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        stream<T1> s = std::move(_f.s);
        uint64_t n = _f.n;
        if (n <= 0) {
          _result = List<T1>::nil();
        } else {
          uint64_t n_ = n - 1;
          _stack.emplace_back(_Resume_n_{hd<T1>(s)});
          _stack.emplace_back(_Enter{tl<T1>(s), n_});
        }
      } else {
        auto _f = std::move(std::get<_Resume_n_>(_frame));
        _result = List<T1>::cons(_f.s, std::move(_result));
      }
    }
    return _result;
  }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, T1 &>
  static stream<T1> iterate(F0 &&f, T1 x) {
    return stream<T1>::lazy_([=]() mutable -> stream<T1> {
      return stream<T1>::scons(x, iterate<T1>(f, f(x)));
    });
  }

  template <typename T1, typename T2, typename F0>
    requires std::is_invocable_r_v<T2, F0 &, T1 &>
  static stream<T2> smap(F0 &&f, stream<T1> s) {
    return stream<T2>::lazy_([=]() mutable -> stream<T2> {
      return stream<T2>::scons(f(hd<T1>(s)), smap<T1, T2>(f, tl<T1>(s)));
    });
  }

  template <typename T1, typename T2, typename T3, typename F0>
    requires std::is_invocable_r_v<T3, F0 &, T1 &, T2 &>
  static stream<T3> zipWith(F0 &&f, stream<T1> s1, stream<T2> s2) {
    return stream<T3>::lazy_([=]() mutable -> stream<T3> {
      return stream<T3>::scons(f(hd<T1>(s1), hd<T2>(s2)),
                               zipWith<T1, T2, T3>(f, tl<T1>(s1), tl<T2>(s2)));
    });
  }

  template <typename T1, typename T2, typename F0>
    requires std::is_invocable_r_v<std::pair<T1, T2>, F0 &, T2 &>
  static stream<T1> unfold(F0 &&f, const T2 &seed) {
    auto [a, s_] = f(seed);
    return stream<T1>::lazy_([=]() mutable -> stream<T1> {
      return stream<T1>::scons(a, unfold<T1, T2>(f, s_));
    });
  }

  static inline const stream<uint64_t> nats =
      iterate<uint64_t>([](uint64_t x) { return (x + 1); }, UINT64_C(0));
  static inline const stream<uint64_t> doubled = smap<uint64_t, uint64_t>(
      [](uint64_t n) { return (n * UINT64_C(2)); }, nats);
  static inline const stream<uint64_t> sum_stream =
      zipWith<uint64_t, uint64_t, uint64_t>(
          [](uint64_t _x0, uint64_t _x1) -> uint64_t { return (_x0 + _x1); },
          nats, doubled);
  static inline const stream<uint64_t> fibs =
      unfold<uint64_t, std::pair<uint64_t, uint64_t>>(
          [](std::pair<uint64_t, uint64_t> pat) {
            const auto &[a, b] = pat;
            return std::make_pair(a, std::make_pair(b, (a + b)));
          },
          std::make_pair(UINT64_C(0), UINT64_C(1)));
  static inline const List<uint64_t> test_nats_5 =
      take<uint64_t>(UINT64_C(5), nats);
  static inline const List<uint64_t> test_doubled_5 =
      take<uint64_t>(UINT64_C(5), doubled);
  static inline const List<uint64_t> test_sum_5 =
      take<uint64_t>(UINT64_C(5), sum_stream);
  static inline const List<uint64_t> test_fibs_8 =
      take<uint64_t>(UINT64_C(8), fibs);
};

#endif // INCLUDED_LOOPIFY_COIND_STREAM
