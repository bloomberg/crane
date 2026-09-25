#ifndef INCLUDED_BIND_CONTINUATION_BINDER_CTOR_ORDER
#define INCLUDED_BIND_CONTINUATION_BINDER_CTOR_ORDER

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

struct Nat;
template <typename A> struct List;
template <typename A> struct EOU;
struct EOU_monad;
template <typename tag, typename addr> struct Dv;
struct Byte;
struct natParams;

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
      this->v_ =
          Cons{[&]() -> A {
                 if constexpr (crane_convertible<A, const _U &>) {
                   return crane_convert<A>(a);
                 } else {
                   throw std::logic_error("unreachable: inactive constructor "
                                          "field at this instantiation");
                 }
               }(),
               (l ? std::make_shared<List<A>>(crane_convert<List<A>>(*l))
                  : nullptr)};
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

  Nat length() const {
    std::shared_ptr<Nat> _head{};
    std::shared_ptr<Nat> *_write = &_head;
    const List<A> *_loop_self = this;
    while (true) {
      auto &&_sv = *_loop_self;
      if (std::holds_alternative<typename List<A>::Nil>(_sv.v())) {
        *_write = std::make_shared<Nat>(Nat::o());
        break;
      } else {
        const auto &[a0, a1] = std::get<typename List<A>::Cons>(_sv.v());
        auto _cell = std::make_shared<Nat>(typename Nat::S(nullptr));
        *_write = std::move(_cell);
        _write = &std::get<typename Nat::S>((*_write)->v_mut()).a0;
        _loop_self = crane_raw(a1);
        continue;
      }
    }
    return std::move(*_head);
  }
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

template <typename A> struct EOU {
  // TYPES
  struct Ok {
    A a0;
  };

  struct Err {
    Nat a0;
  };

  using variant_t = std::variant<Ok, Err>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  EOU() {}

  explicit EOU(Ok _v) : v_(std::move(_v)) {}

  explicit EOU(Err _v) : v_(std::move(_v)) {}

  template <typename _U> EOU(const EOU<_U> &_other) {
    if (std::holds_alternative<typename EOU<_U>::Ok>(_other.v())) {
      const auto &[a0] = std::get<typename EOU<_U>::Ok>(_other.v());
      this->v_ = Ok{[&]() -> A {
        if constexpr (crane_convertible<A, const _U &>) {
          return crane_convert<A>(a0);
        } else {
          throw std::logic_error(
              "unreachable: inactive constructor field at this instantiation");
        }
      }()};
    } else {
      const auto &[a0] = std::get<typename EOU<_U>::Err>(_other.v());
      this->v_ = Err{a0};
    }
  }

  static EOU<A> ok(A a0) { return EOU<A>(Ok{std::move(a0)}); }

  static EOU<A> err(Nat a0) { return EOU<A>(Err{std::move(a0)}); }

  // MANIPULATORS
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

struct EOU_monad {
  template <typename _A0> using m = EOU<_A0>;

  template <typename _A0> static EOU<_A0> ret(_A0 a) {
    return EOU<_A0>::ok(std::move(a));
  }

  template <typename _A0, typename _A1>
  static EOU<_A1> bind(EOU<_A0> m, std::function<EOU<_A1>(_A0)> k) {
    if (std::holds_alternative<typename EOU<_A0>::Ok>(m.v())) {
      const auto &[a00] = std::get<typename EOU<_A0>::Ok>(m.v());
      return k(a00);
    } else {
      const auto &[a00] = std::get<typename EOU<_A0>::Err>(m.v());
      return EOU<_A1>::err(a00);
    }
  }
};

static_assert(Monad<EOU_monad>);
template <typename
I>concept Params = requires {
  typename I::addr;
  typename I::tag;
} && (requires {
  { I::zero() } -> std::convertible_to<typename I::addr>;
} || requires {
  { I::zero } -> std::convertible_to<typename I::addr>;
}) && (requires {
  { I::t0() } -> std::convertible_to<typename I::tag>;
} || requires {
  { I::t0 } -> std::convertible_to<typename I::tag>;
});
using addr = std::any;
using tag = std::any;

/// Two class-dependent fields, the second-declared one first in DAddr.
template <typename tag, typename addr> struct Dv {
  // TYPES
  struct DAddr {
    tag a0;
    addr a1;
  };

  struct DNum {
    Nat a0;
  };

  using variant_t = std::variant<DAddr, DNum>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  Dv() {}

  explicit Dv(DAddr _v) : v_(std::move(_v)) {}

  explicit Dv(DNum _v) : v_(std::move(_v)) {}

  template <typename _U0, typename _U1> Dv(const Dv<_U0, _U1> &_other) {
    if (std::holds_alternative<typename Dv<_U0, _U1>::DAddr>(_other.v())) {
      const auto &[a0, a1] = std::get<typename Dv<_U0, _U1>::DAddr>(_other.v());
      this->v_ = DAddr{a0, a1};
    } else {
      const auto &[a0] = std::get<typename Dv<_U0, _U1>::DNum>(_other.v());
      this->v_ = DNum{a0};
    }
  }

  static Dv<tag, addr> daddr(tag a0, addr a1) {
    return Dv<tag, addr>(DAddr{std::move(a0), std::move(a1)});
  }

  static Dv<tag, addr> dnum(Nat a0) {
    return Dv<tag, addr>(DNum{std::move(a0)});
  }

  // MANIPULATORS
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

struct Byte {
  // DATA
  Nat a0;

  // ACCESSORS
  Byte clone() const { return {a0}; }

  // CREATORS
  static Byte b(Nat a0) { return {std::move(a0)}; }
};

template <Params _tcI0>
EOU<Dv<typename _tcI0::tag, typename _tcI0::addr>>
bytes_to_dv(const Nat &n, const List<Byte> &bs) {
  if (std::holds_alternative<typename Nat::O>(n.v())) {
    return Monad0::template ret<EOU_monad,
                                Dv<typename _tcI0::tag, typename _tcI0::addr>>(
        Dv<typename _tcI0::tag, typename _tcI0::addr>::dnum(Nat::o()));
  } else {
    const auto &[a0] = std::get<typename Nat::S>(n.v());
    const Nat &a0_value = *a0;
    if (std::holds_alternative<typename List<Byte>::Nil>(bs.v())) {
      return Monad0::template ret<
          EOU_monad, Dv<typename _tcI0::tag, typename _tcI0::addr>>(
          Dv<typename _tcI0::tag, typename _tcI0::addr>::daddr(_tcI0::t0(),
                                                               _tcI0::zero()));
    } else {
      const auto &[a00, a10] = std::get<typename List<Byte>::Cons>(bs.v());
      const List<Byte> &a10_value = *a10;
      const auto &[a01] = a00;
      auto go_impl = [&](auto &_self_go, const List<Nat> &ds,
                         const List<Byte> &bs0)
          -> EOU<List<Dv<typename _tcI0::tag, typename _tcI0::addr>>> {
        if (std::holds_alternative<typename List<Nat>::Nil>(ds.v())) {
          return Monad0::template ret<
              EOU_monad, List<Dv<typename _tcI0::tag, typename _tcI0::addr>>>(
              List<Dv<typename _tcI0::tag, typename _tcI0::addr>>::nil());
        } else {
          const auto &[a02, a12] = std::get<typename List<Nat>::Cons>(ds.v());
          const List<Nat> &a12_value = *a12;
          return Monad0::template bind<
              EOU_monad, Dv<typename _tcI0::tag, typename _tcI0::addr>,
              List<Dv<typename _tcI0::tag, typename _tcI0::addr>>>(
              bytes_to_dv<_tcI0>(a0_value, bs0),
              [=](Dv<typename _tcI0::tag, typename _tcI0::addr> f) mutable {
                return Monad0::template bind<
                    EOU_monad,
                    List<Dv<typename _tcI0::tag, typename _tcI0::addr>>,
                    List<Dv<typename _tcI0::tag, typename _tcI0::addr>>>(
                    _self_go(_self_go, a12_value, bs0),
                    [=](const auto &r) mutable {
                      return Monad0::template ret<
                          EOU_monad,
                          List<Dv<typename _tcI0::tag, typename _tcI0::addr>>>(
                          List<Dv<typename _tcI0::tag,
                                  typename _tcI0::addr>>::cons(f, r));
                    });
              });
        }
      };
      auto go = [&](const List<Nat> &ds, const List<Byte> &bs0)
          -> EOU<List<Dv<typename _tcI0::tag, typename _tcI0::addr>>> {
        return go_impl(go_impl, ds, bs0);
      };
      return Monad0::template bind<
          EOU_monad, List<Dv<typename _tcI0::tag, typename _tcI0::addr>>,
          Dv<typename _tcI0::tag, typename _tcI0::addr>>(
          go(List<Nat>::cons(a01, List<Nat>::nil()), a10_value),
          [](const List<Dv<typename _tcI0::tag, typename _tcI0::addr>> &r) {
            return Monad0::template ret<
                EOU_monad, Dv<typename _tcI0::tag, typename _tcI0::addr>>(
                Dv<typename _tcI0::tag, typename _tcI0::addr>::dnum(
                    r.length()));
          });
    }
  }
}

struct natParams {
  using addr = Nat;
  using tag = bool;

  static Nat zero() { return Nat::o(); }

  constexpr static bool t0() { return true; }
};

static_assert(Params<natParams>);

struct BindContinuationBinderCtorOrder {
  static inline const EOU<Dv<typename natParams::tag, typename natParams::addr>>
      run = bytes_to_dv<natParams>(
          Nat::s(Nat::s(Nat::o())),
          List<Byte>::cons(Byte::b(Nat::s(Nat::o())), List<Byte>::nil()));
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

#endif // INCLUDED_BIND_CONTINUATION_BINDER_CTOR_ORDER
