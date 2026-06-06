#ifndef INCLUDED_STREAM
#define INCLUDED_STREAM

#include "lazy.h"
#include <any>
#include <functional>
#include <memory>
#include <utility>
#include <variant>
#include <vector>

struct Nat {
  // TYPES
  struct O {};

  struct S {
    std::shared_ptr<Nat> a0;
  };

  using variant_t = std::variant<O, S>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  Nat() {}

  explicit Nat(O _v) : v_(_v) {}

  explicit Nat(S _v) : v_(std::move(_v)) {}

  static Nat o() { return Nat(O{}); }

  static Nat s(Nat a0) { return Nat(S{std::make_shared<Nat>(std::move(a0))}); }

  // MANIPULATORS
  ~Nat() {
    std::vector<std::shared_ptr<Nat>> _stack = {};
    auto _drain = [&](variant_t &_v) {
      if (auto *_alt = std::get_if<S>(&_v)) {
        if (_alt->a0) {
          _stack.push_back(std::move(_alt->a0));
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

template <typename A> struct Stream {
  // TYPES
  struct Scons {
    A x;
    std::shared_ptr<Stream<A>> xs;
  };

  using variant_t = std::variant<Scons>;

private:
  // DATA
  crane::lazy<variant_t> lazy_v_;

public:
  // CREATORS
  explicit Stream(Scons _v)
      : lazy_v_(crane::lazy<variant_t>(variant_t(std::move(_v)))) {}

  explicit Stream(std::function<variant_t()> _thunk)
      : lazy_v_(crane::lazy<variant_t>(std::move(_thunk))) {}

  static Stream<A> scons(A x, const Stream<A> &xs) {
    return Stream(Scons{std::move(x), std::make_shared<Stream<A>>(xs)});
  }

  static Stream<A> lazy_(std::function<Stream<A>()> thunk) {
    return Stream<A>(std::function<variant_t()>([=]() mutable -> variant_t {
      Stream<A> _tmp = thunk();
      return _tmp.v();
    }));
  }

  // ACCESSORS
  const variant_t &v() const { return lazy_v_.force(); }

  Stream<A> interleave(Stream<A> sb) const {
    const auto &[a0, a1] = std::get<typename Stream<A>::Scons>(this->v());
    return Stream<A>::lazy_([=]() mutable -> Stream<A> {
      return Stream<A>::scons(a0, sb.interleave(*a1));
    });
  }

  template <typename T1> static List<T1> take(const Nat &n, Stream<T1> s) {
    if (std::holds_alternative<typename Nat::O>(n.v())) {
      return List<T1>::nil();
    } else {
      const auto &[a0] = std::get<typename Nat::S>(n.v());
      const auto &[a00, a10] = std::get<typename Stream<T1>::Scons>(s.v());
      return List<T1>::cons(a00, take<T1>(*a0, *a10));
    }
  }

  template <typename T1> static Stream<T1> repeat(T1 x) {
    return Stream<T1>::lazy_([=]() mutable -> Stream<T1> {
      return Stream<T1>::scons(x, repeat<T1>(x));
    });
  }

  static Stream<Nat> nats_from(Nat n) {
    return Stream<Nat>::lazy_([=]() mutable -> Stream<Nat> {
      return Stream<Nat>::scons(n, nats_from(Nat::s(n)));
    });
  }

  static const Stream<Nat> &ones() {
    static const Stream<Nat> v = repeat<Nat>(Nat::s(Nat::o()));
    return v;
  }

  static const List<Nat> &first_five_nats() {
    static const List<Nat> v = take<Nat>(
        Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::o()))))), nats_from(Nat::o()));
    return v;
  }

  static const List<Nat> &first_five_ones() {
    static const List<Nat> v =
        take<Nat>(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::o()))))), ones());
    return v;
  }

  static const List<Nat> &interleaved() {
    static const List<Nat> v = take<Nat>(
        Nat::s(
            Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::o())))))))),
        nats_from(Nat::o()).interleave(repeat<Nat>(
            Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::o()))))))))));
    return v;
  }
};

#endif // INCLUDED_STREAM
