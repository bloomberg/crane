#ifndef INCLUDED_HKT_NULLARY_METHOD_TYARG
#define INCLUDED_HKT_NULLARY_METHOD_TYARG

#include "crane_fn.h"
#include "small_vector.h"
#include <any>
#include <atomic>
#include <concepts>
#include <memory>
#include <utility>
#include <variant>

struct Nat;
template <typename A> struct List;

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
    crane::small_vector<std::shared_ptr<Nat>> _stack = {};
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
        std::atomic_thread_fence(std::memory_order_acquire);
        _drain(_cur->v_mut());
      }
    }
  }

  Nat(const Nat &) = default;
  Nat &operator=(const Nat &) = default;
  Nat(Nat &&) noexcept = default;
  Nat &operator=(Nat &&) noexcept = default;

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

  template <typename _U> List(const List<_U> &_other) {
    if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
      this->v_ = Nil{};
    } else {
      const auto &[a, l] = std::get<typename List<_U>::Cons>(_other.v());
      this->v_ = Cons{[&]() -> A {
                        if constexpr (std::is_same_v<_U, std::any>)
                          return crane_any_cast<A>(a);
                        else
                          return A(a);
                      }(),
                      l ? std::make_shared<List<A>>(*l) : nullptr};
    }
  }

  static List<A> nil() { return List<A>(Nil{}); }

  static List<A> cons(A a, List<A> l) {
    return List<A>(Cons{std::move(a), std::make_shared<List<A>>(std::move(l))});
  }

  // MANIPULATORS
  ~List() {
    crane::small_vector<std::shared_ptr<List<A>>> _stack = {};
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
        std::atomic_thread_fence(std::memory_order_acquire);
        _drain(_cur->v_mut());
      }
    }
  }

  List(const List &) = default;
  List &operator=(const List &) = default;
  List(List &&) noexcept = default;
  List &operator=(List &&) noexcept = default;

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

/// emptyc takes no value argument, so its element type is not deducible and
/// must be passed explicitly.  The generic body omits it:
///
/// return sizec<_tcI0>(addc<_tcI0>(x, addc<_tcI0>(y, emptyc<_tcI0>())));
///
/// error: no matching function for call to 'emptyc'
/// (the wrapper is declared template <Coll _tcI0, typename T2>)
template <typename I>
concept Coll = requires {
  typename I::template C<std::any>;
  {
    I::template emptyc<std::any>()
  } -> std::convertible_to<typename I::template C<std::any>>;
  {
    I::template addc<std::any>(std::declval<std::any>(),
                               std::declval<typename I::template C<std::any>>())
  } -> std::convertible_to<typename I::template C<std::any>>;
  {
    I::template sizec<std::any>(
        std::declval<typename I::template C<std::any>>())
  } -> std::convertible_to<Nat>;
};

struct HktNullaryMethodTyarg {
  template <Coll _tcI0, typename T2>
  static typename _tcI0::template C<T2> emptyc() {
    return _tcI0::template emptyc<T2>();
  }

  template <Coll _tcI0, typename T2>
  static typename _tcI0::template C<T2>
  addc(const T2 &x, typename _tcI0::template C<T2> x0) {
    return _tcI0::template addc<T2>(x, x0);
  }

  template <Coll _tcI0, typename T2>
  static Nat sizec(typename _tcI0::template C<T2> x) {
    return _tcI0::template sizec<T2>(x);
  }

  template <typename T1> static Nat llen(const List<T1> &l) {
    if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
      return Nat::o();
    } else {
      const auto &[a0, a1] = std::get<typename List<T1>::Cons>(l.v());
      return Nat::s(llen<T1>(*a1));
    }
  }

  struct LC {
    template <typename _A0> using C = List<_A0>;

    template <typename _A0> static List<_A0> emptyc() {
      return List<_A0>::nil();
    }

    template <typename _A0> static List<_A0> addc(_A0 x, List<_A0> l) {
      return List<_A0>::cons(x, l);
    }

    template <typename _A0> static Nat sizec(List<_A0> a0) {
      return llen<_A0>(a0);
    }
  };

  static_assert(Coll<LC>);

  template <Coll _tcI0, typename T2> static Nat two(const T2 &x, const T2 &y) {
    return sizec<_tcI0, T2>(
        addc<_tcI0, T2>(x, addc<_tcI0, T2>(y, emptyc<_tcI0, T2>())));
  }

  static inline const Nat run =
      two<LC, Nat>(Nat::s(Nat::o()), Nat::s(Nat::s(Nat::o())));
};

#endif // INCLUDED_HKT_NULLARY_METHOD_TYARG
