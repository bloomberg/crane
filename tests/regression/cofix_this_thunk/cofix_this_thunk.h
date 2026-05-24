#ifndef INCLUDED_COFIX_THIS_THUNK
#define INCLUDED_COFIX_THIS_THUNK

#include "lazy.h"
#include <any>
#include <functional>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

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
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

/// Module name "Sseq" matches coinductive "sseq" -> eponymous
template <typename A> struct Sseq {
  // TYPES
  struct SCons {
    A shead;
    std::shared_ptr<Sseq<A>> stail;
  };

  using variant_t = std::variant<SCons>;

private:
  // DATA
  crane::lazy<variant_t> lazy_v_;

public:
  // CREATORS
  explicit Sseq(SCons _v)
      : lazy_v_(crane::lazy<variant_t>(variant_t(std::move(_v)))) {}

  explicit Sseq(std::function<variant_t()> _thunk)
      : lazy_v_(crane::lazy<variant_t>(std::move(_thunk))) {}

  static Sseq<A> scons(A shead, const Sseq<A> &stail) {
    return Sseq(SCons{std::move(shead), std::make_shared<Sseq<A>>(stail)});
  }

  static Sseq<A> lazy_(std::function<Sseq<A>()> thunk) {
    return Sseq<A>(std::function<variant_t()>([=]() mutable -> variant_t {
      Sseq<A> _tmp = thunk();
      return _tmp.v();
    }));
  }

  // ACCESSORS
  const variant_t &v() const { return lazy_v_.force(); }

  A shead() const {
    const auto &[shead1, stail0] = std::get<typename Sseq<A>::SCons>(this->v());
    return shead1;
  }

  Sseq<A> stail() const {
    const auto &[shead0, stail1] = std::get<typename Sseq<A>::SCons>(this->v());
    return Sseq<A>::lazy_([=]() mutable -> Sseq<A> { return *stail1; });
  }

  /// This will be methodified on sseq because first arg is sseq A
  /// and the module is eponymous.
  template <typename F0>
    requires std::is_invocable_r_v<A, F0 &, A &>
  A double_head(F0 &&f) const {
    return f(this->shead());
  }

  template <typename F0>
    requires std::is_invocable_r_v<A, F0 &, A &>
  Sseq<A> smap(F0 &&f) const {
    Sseq<A> _self_val = *this;
    return Sseq<A>::lazy_([=]() mutable -> Sseq<A> {
      return Sseq<A>::scons(_self_val.double_head(f),
                            _self_val.stail().smap(f));
    });
  }

  template <typename F0>
    requires std::is_invocable_r_v<A, F0 &, A &>
  Sseq<A> smap_direct(F0 &&f) const {
    Sseq<A> _self_val = *this;
    return Sseq<A>::lazy_([=]() mutable -> Sseq<A> {
      return Sseq<A>::scons(f(_self_val.shead()),
                            _self_val.stail().smap_direct(f));
    });
  }

  /// Take n elements
  List<A> take(uint64_t n) const {
    if (n <= 0) {
      return List<A>::nil();
    } else {
      uint64_t m = n - 1;
      return List<A>::cons(this->shead(), this->stail().take(m));
    }
  }

  static Sseq<uint64_t> nats_from(uint64_t n) {
    return Sseq<uint64_t>::lazy_([=]() mutable -> Sseq<uint64_t> {
      return Sseq<uint64_t>::scons(n, nats_from((n + 1)));
    });
  }

  /// Sum of a list
  static uint64_t sum(const List<uint64_t> &l) {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
      return UINT64_C(0);
    } else {
      const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
      return (a0 + sum(*a1));
    }
  }

  /// test1: smap (nats_from 0) S gives 1, 2, 3, 4, ...
  /// take 4 -> 1, 2, 3, 4 -> sum = 10
  static const uint64_t &test1() {
    static const uint64_t v = []() {
      Sseq<uint64_t> s =
          nats_from(UINT64_C(0)).smap([](uint64_t x) { return (x + 1); });
      return sum(s.take(UINT64_C(4)));
    }();
    return v;
  }

  /// test2: smap_direct (nats_from 0) S gives 1, 2, 3, 4, ...
  /// take 4 -> 1, 2, 3, 4 -> sum = 10
  static const uint64_t &test2() {
    static const uint64_t v = []() {
      Sseq<uint64_t> s = nats_from(UINT64_C(0)).smap_direct([](uint64_t x) {
        return (x + 1);
      });
      return sum(s.take(UINT64_C(4)));
    }();
    return v;
  }
};

#endif // INCLUDED_COFIX_THIS_THUNK
