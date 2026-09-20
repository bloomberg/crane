#ifndef INCLUDED_INSTANCE_HOISTED_OVER_QUALIFIED
#define INCLUDED_INSTANCE_HOISTED_OVER_QUALIFIED

#include "crane_fn.h"
#include "small_vector.h"
#include <any>
#include <atomic>
#include <concepts>
#include <functional>
#include <memory>
#include <stdexcept>
#include <type_traits>
#include <utility>
#include <variant>

struct EOUP_Monad;
struct Nat;
template <typename A, typename B> struct Sum;
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

  Nat add(Nat m) const {
    std::shared_ptr<Nat> _head{};
    std::shared_ptr<Nat> *_write = &_head;
    const Nat *_loop_self = this;
    Nat _loop_m = std::move(m);
    while (true) {
      auto &&_sv = *_loop_self;
      if (std::holds_alternative<typename Nat::O>(_sv.v())) {
        *_write = std::make_shared<Nat>(std::move(_loop_m));
        break;
      } else {
        const auto &[a0] = std::get<typename Nat::S>(_sv.v());
        auto _cell = std::make_shared<Nat>(typename Nat::S(nullptr));
        *_write = std::move(_cell);
        _write = &std::get<typename Nat::S>((*_write)->v_mut()).a0;
        _loop_self = crane_raw(a0);
        continue;
      }
    }
    return std::move(*_head);
  }
};

template <typename A, typename B> struct Sum {
  // TYPES
  struct Inl {
    A a0;
  };

  struct Inr {
    B a0;
  };

  using variant_t = std::variant<Inl, Inr>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  Sum() {}

  explicit Sum(Inl _v) : v_(std::move(_v)) {}

  explicit Sum(Inr _v) : v_(std::move(_v)) {}

  template <typename _U0, typename _U1> Sum(const Sum<_U0, _U1> &_other) {
    if (std::holds_alternative<typename Sum<_U0, _U1>::Inl>(_other.v())) {
      const auto &[a0] = std::get<typename Sum<_U0, _U1>::Inl>(_other.v());
      this->v_ = Inl{[&]() -> A {
        if constexpr (std::is_same_v<_U0, std::any>) {
          return crane_any_cast<A>(a0);
        } else {
          if constexpr (std::is_constructible_v<A, const _U0 &>) {
            return A(a0);
          } else {
            throw std::logic_error("unreachable: inactive constructor field at "
                                   "this instantiation");
          }
        }
      }()};
    } else {
      const auto &[a0] = std::get<typename Sum<_U0, _U1>::Inr>(_other.v());
      this->v_ = Inr{[&]() -> B {
        if constexpr (std::is_same_v<_U1, std::any>) {
          return crane_any_cast<B>(a0);
        } else {
          if constexpr (std::is_constructible_v<B, const _U1 &>) {
            return B(a0);
          } else {
            throw std::logic_error("unreachable: inactive constructor field at "
                                   "this instantiation");
          }
        }
      }()};
    }
  }

  static Sum<A, B> inl(A a0) { return Sum<A, B>(Inl{std::move(a0)}); }

  static Sum<A, B> inr(B a0) { return Sum<A, B>(Inr{std::move(a0)}); }

  // MANIPULATORS
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
      this->v_ =
          Cons{[&]() -> A {
                 if constexpr (std::is_same_v<_U, std::any>) {
                   return crane_any_cast<A>(a);
                 } else {
                   if constexpr (std::is_constructible_v<A, const _U &>) {
                     return A(a);
                   } else {
                     throw std::logic_error("unreachable: inactive constructor "
                                            "field at this instantiation");
                   }
                 }
               }(),
               (l ? std::make_shared<List<A>>(*l) : nullptr)};
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

template <typename I>
concept Monad = requires {
  typename I::template m<std::any>;
  {
    I::template ret<std::any>(std::declval<std::any>())
  } -> std::convertible_to<typename I::template m<std::any>>;
  {
    I::template bind<std::any, std::any>(
        std::declval<typename I::template m<std::any>>(),
        std::declval<
            std::function<typename I::template m<std::any>(std::any)>>())
  } -> std::convertible_to<typename I::template m<std::any>>;
};

struct Monad0 {
  template <Monad _tcI0, typename T2>
  static typename _tcI0::template m<T2> ret(const T2 &x);
  template <Monad _tcI0, typename T2, typename T3, typename F1>
    requires std::is_invocable_r_v<typename _tcI0::template m<T3>, F1 &, T2 &>
  static typename _tcI0::template m<T3> bind(typename _tcI0::template m<T2> x,
                                             F1 &&x0);
};

struct Eou {
  static Nat helper(Nat n);
};

template <typename a> using EOUP = Sum<Nat, a>;

struct MemoryBytes {
  template <Monad _tcI0, typename T2, typename T3, typename F0>
    requires std::is_invocable_r_v<typename _tcI0::template m<T3>, F0 &, T2 &>
  static typename _tcI0::template m<List<T3>> map_monad(F0 &&f,
                                                        const List<T2> &l);
  static Nat helper0(Nat n);
  static EOUP<List<Nat>> bump_all(const List<Nat> &bs);
};

struct EOUP_Monad {
  template <typename _A0> using m = Sum<Nat, _A0>;

  template <typename _A0> static Sum<Nat, _A0> ret(_A0 a) {
    return Sum<Nat, _A0>::inr(std::move(a));
  }

  template <typename _A0, typename _A1>
  static Sum<Nat, _A1> bind(Sum<Nat, _A0> m,
                            std::function<Sum<Nat, _A1>(_A0)> k) {
    if (std::holds_alternative<typename Sum<Nat, _A0>::Inl>(m.v())) {
      const auto &[a0] = std::get<typename Sum<Nat, _A0>::Inl>(m.v());
      return Sum<Nat, _A1>::inl(a0);
    } else {
      const auto &[a0] = std::get<typename Sum<Nat, _A0>::Inr>(m.v());
      return std::move(k)(a0);
    }
  }
};

static_assert(Monad<EOUP_Monad>);

struct InstanceHoistedOverQualified {
  static std::pair<Nat, EOUP<List<Nat>>> use(const List<Nat> &bs);
};

template <Monad _tcI0, typename T2>
typename _tcI0::template m<T2> Monad0::ret(const T2 &x) {
  return _tcI0::template ret<T2>(x);
}

template <Monad _tcI0, typename T2, typename T3, typename F1>
  requires std::is_invocable_r_v<typename _tcI0::template m<T3>, F1 &, T2 &>
typename _tcI0::template m<T3> Monad0::bind(typename _tcI0::template m<T2> x,
                                            F1 &&x0) {
  return _tcI0::template bind<T2, T3>(std::move(x), x0);
}

template <Monad _tcI0, typename T2, typename T3, typename F0>
  requires std::is_invocable_r_v<typename _tcI0::template m<T3>, F0 &, T2 &>
typename _tcI0::template m<List<T3>> MemoryBytes::map_monad(F0 &&f,
                                                            const List<T2> &l) {
  if (std::holds_alternative<typename List<T2>::Nil>(l.v())) {
    return Monad0::template ret<_tcI0, List<T3>>(List<T3>::nil());
  } else {
    const auto &[a0, a1] = std::get<typename List<T2>::Cons>(l.v());
    const List<T2> &a1_value = *a1;
    return Monad0::template bind<_tcI0, T3, List<T3>>(f(a0), [=](T3 y) mutable {
      return Monad0::template bind<_tcI0, List<T3>, List<T3>>(
          MemoryBytes::template map_monad<_tcI0, T2, T3>(f, a1_value),
          [=](const auto &ys) mutable {
            return Monad0::template ret<_tcI0, List<T3>>(List<T3>::cons(y, ys));
          });
    });
  }
}

#endif // INCLUDED_INSTANCE_HOISTED_OVER_QUALIFIED
