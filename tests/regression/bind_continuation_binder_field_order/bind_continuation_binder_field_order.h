#ifndef INCLUDED_BIND_CONTINUATION_BINDER_FIELD_ORDER
#define INCLUDED_BIND_CONTINUATION_BINDER_FIELD_ORDER

#include "crane_fn.h"
#include "fn.h"
#include "obj.h"
#include <atomic>
#include <concepts>
#include <memory>
#include <optional>
#include <stdexcept>
#include <utility>
#include <variant>

struct Nat;
template <typename A> struct List;
template <typename A> struct EOU;
struct EOU_monad;
template <typename tag, typename addr> struct Dv;
struct Byte;
struct natParams;
using tag = crane::obj;
using addr = crane::obj;
template <typename I>
concept Monad = requires {
  typename I::template m<crane::obj>;
  {
    I::template ret<crane::obj>(std::declval<crane::obj>())
  } -> std::convertible_to<typename I::template m<crane::obj>>;
  {
    I::template bind<crane::obj, crane::obj>(
        std::declval<typename I::template m<crane::obj>>(),
        std::declval<
            crane::fn<typename I::template m<crane::obj>(crane::obj)>>())
  } -> std::convertible_to<typename I::template m<crane::obj>>;
};
/// The only difference from the file next door: tag is declared first.
template <typename
I>concept Params = requires {
    typename I::tag;
    typename I::addr;
  } && (requires {
    { I::t0() } -> std::convertible_to<typename I::tag>;
  } || requires {
    { I::t0 } -> std::convertible_to<typename I::tag>;
  }) && (requires {
    { I::zero() } -> std::convertible_to<typename I::addr>;
  } || requires {
    { I::zero } -> std::convertible_to<typename I::addr>;
  });

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
    auto _next = [&](variant_t &_v) -> std::shared_ptr<Nat> {
      if (auto *_alt = std::get_if<S>(&_v)) {
        if (_alt->a0 && _alt->a0.use_count() == 1) {
          std::atomic_thread_fence(std::memory_order_acquire);
          return std::move(_alt->a0);
        }
      }
      return nullptr;
    };
    std::shared_ptr<Nat> _cur = _next(v_mut());
    while (_cur) {
      _cur = _next(_cur->v_mut());
    }
  }

  Nat(const Nat &) = default;
  Nat &operator=(const Nat &) = default;
  Nat(Nat &&) = default;
  Nat &operator=(Nat &&) = default;

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

  template <typename CraneU>
  List(const List<CraneU> &_other)
      : v_([&]() -> variant_t {
          if (std::holds_alternative<typename List<CraneU>::Nil>(_other.v())) {
            return Nil{};
          } else {
            const auto &[a, l] =
                std::get<typename List<CraneU>::Cons>(_other.v());
            return Cons{
                [&]() -> A {
                  if constexpr (crane_convertible<A, const CraneU &>) {
                    return crane_convert<A>(a);
                  } else {
                    throw std::logic_error("unreachable: inactive constructor "
                                           "field at this instantiation");
                  }
                }(),
                (l ? std::make_shared<List<A>>(crane_convert<List<A>>(*l))
                   : nullptr)};
          }
        }()) {}

  static List<A> nil() { return List<A>(Nil{}); }

  static List<A> cons(A a, List<A> l) {
    return List<A>(Cons{std::move(a), std::make_shared<List<A>>(std::move(l))});
  }

  // MANIPULATORS
  ~List() {
    auto _next = [&](variant_t &_v) -> std::shared_ptr<List<A>> {
      if (auto *_alt = std::get_if<Cons>(&_v)) {
        if (_alt->l && _alt->l.use_count() == 1) {
          std::atomic_thread_fence(std::memory_order_acquire);
          return std::move(_alt->l);
        }
      }
      return nullptr;
    };
    std::shared_ptr<List<A>> _cur = _next(v_mut());
    while (_cur) {
      _cur = _next(_cur->v_mut());
    }
  }

  List(const List &) = default;
  List &operator=(const List &) = default;
  List(List &&) = default;
  List &operator=(List &&) = default;

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  Nat length() const {
    std::optional<Nat> _root{};
    std::shared_ptr<Nat> *_write = nullptr;
    const List<A> *_loop_self = this;
    while (true) {
      auto &&_sv = *_loop_self;
      if (std::holds_alternative<typename List<A>::Nil>(_sv.v())) {
        auto _value = Nat::o();
        (_write ? *(*_write = std::make_shared<Nat>(std::move(_value)))
                : _root.emplace(std::move(_value)));
        break;
      } else {
        const auto &[a0, a1] = std::get<typename List<A>::Cons>(_sv.v());
        auto _cell = typename Nat::S(nullptr);
        Nat &_node =
            (_write ? *(*_write = std::make_shared<Nat>(std::move(_cell)))
                    : _root.emplace(std::move(_cell)));
        _write = &std::get<typename Nat::S>(_node.v_mut()).a0;
        _loop_self = crane_raw(a1);
        continue;
      }
    }
    return std::move(*_root);
  }
};

struct Monad0 {
  template <Monad _tcI0, typename T2>
  static typename _tcI0::template m<T2> ret(const T2 &x);
  template <Monad _tcI0, typename T2, typename T3, typename F1>
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

  template <typename CraneU>
  EOU(const EOU<CraneU> &_other)
      : v_([&]() -> variant_t {
          if (std::holds_alternative<typename EOU<CraneU>::Ok>(_other.v())) {
            const auto &[a0] = std::get<typename EOU<CraneU>::Ok>(_other.v());
            return Ok{[&]() -> A {
              if constexpr (crane_convertible<A, const CraneU &>) {
                return crane_convert<A>(a0);
              } else {
                throw std::logic_error("unreachable: inactive constructor "
                                       "field at this instantiation");
              }
            }()};
          } else {
            const auto &[a0] = std::get<typename EOU<CraneU>::Err>(_other.v());
            return Err{a0};
          }
        }()) {}

  static EOU<A> ok(A a0) { return EOU<A>(Ok{std::move(a0)}); }

  static EOU<A> err(Nat a0) { return EOU<A>(Err{std::move(a0)}); }

  // MANIPULATORS
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

struct EOU_monad {
  template <typename CraneA0> using m = EOU<CraneA0>;

  template <typename CraneA0> static EOU<CraneA0> ret(CraneA0 a) {
    return EOU<CraneA0>::ok(std::move(a));
  }

  template <typename CraneA0, typename CraneA1>
  static EOU<CraneA1> bind(EOU<CraneA0> m, crane::fn<EOU<CraneA1>(CraneA0)> k) {
    if (std::holds_alternative<typename EOU<CraneA0>::Ok>(m.v())) {
      const auto &[a0] = std::get<typename EOU<CraneA0>::Ok>(m.v());
      return k(a0);
    } else {
      const auto &[a0] = std::get<typename EOU<CraneA0>::Err>(m.v());
      return EOU<CraneA1>::err(a0);
    }
  }
};

static_assert(Monad<EOU_monad>);

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

  template <typename CraneU0, typename CraneU1>
  Dv(const Dv<CraneU0, CraneU1> &_other)
      : v_([&]() -> variant_t {
          if (std::holds_alternative<typename Dv<CraneU0, CraneU1>::DAddr>(
                  _other.v())) {
            const auto &[a0, a1] =
                std::get<typename Dv<CraneU0, CraneU1>::DAddr>(_other.v());
            return DAddr{
                [&]() -> tag {
                  if constexpr (crane_convertible<tag, const CraneU0 &>) {
                    return crane_convert<tag>(a0);
                  } else {
                    throw std::logic_error("unreachable: inactive constructor "
                                           "field at this instantiation");
                  }
                }(),
                [&]() -> addr {
                  if constexpr (crane_convertible<addr, const CraneU1 &>) {
                    return crane_convert<addr>(a1);
                  } else {
                    throw std::logic_error("unreachable: inactive constructor "
                                           "field at this instantiation");
                  }
                }()};
          } else {
            const auto &[a0] =
                std::get<typename Dv<CraneU0, CraneU1>::DNum>(_other.v());
            return DNum{a0};
          }
        }()) {}

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
    return EOU_monad::template ret<
        Dv<typename _tcI0::tag, typename _tcI0::addr>>(
        Dv<typename _tcI0::tag, typename _tcI0::addr>::dnum(Nat::o()));
  } else {
    const auto &[a0] = std::get<typename Nat::S>(n.v());
    const Nat &a0_value = *a0;
    if (std::holds_alternative<typename List<Byte>::Nil>(bs.v())) {
      return EOU_monad::template ret<
          Dv<typename _tcI0::tag, typename _tcI0::addr>>(
          Dv<typename _tcI0::tag, typename _tcI0::addr>::daddr(_tcI0::t0(),
                                                               _tcI0::zero()));
    } else {
      const auto &[a00, a10] = std::get<typename List<Byte>::Cons>(bs.v());
      const List<Byte> &a10_value = *a10;
      const auto &[a01] = a00;
      auto go_impl = [=](auto &_self_go, List<Nat> ds, List<Byte> bs0)
          -> EOU<List<Dv<typename _tcI0::tag, typename _tcI0::addr>>> {
        if (std::holds_alternative<typename List<Nat>::Nil>(ds.v())) {
          return EOU_monad::template ret<
              List<Dv<typename _tcI0::tag, typename _tcI0::addr>>>(
              List<Dv<typename _tcI0::tag, typename _tcI0::addr>>::nil());
        } else {
          const auto &[a02, a12] = std::get<typename List<Nat>::Cons>(ds.v());
          const List<Nat> &a12_value = *a12;
          return EOU_monad::template bind<
              Dv<typename _tcI0::tag, typename _tcI0::addr>,
              List<Dv<typename _tcI0::tag, typename _tcI0::addr>>>(
              bytes_to_dv<_tcI0>(a0_value, bs0),
              [=](const Dv<typename _tcI0::tag, typename _tcI0::addr> &f) {
                return EOU_monad::template bind<
                    List<Dv<typename _tcI0::tag, typename _tcI0::addr>>,
                    List<Dv<typename _tcI0::tag, typename _tcI0::addr>>>(
                    _self_go(_self_go, a12_value, bs0),
                    [=](const List<
                        Dv<typename _tcI0::tag, typename _tcI0::addr>> &r) {
                      return EOU_monad::template ret<
                          List<Dv<typename _tcI0::tag, typename _tcI0::addr>>>(
                          List<Dv<typename _tcI0::tag,
                                  typename _tcI0::addr>>::cons(f, r));
                    });
              });
        }
      };
      auto go = [=, go_impl = std::move(go_impl)](List<Nat> ds, List<Byte> bs0)
          -> EOU<List<Dv<typename _tcI0::tag, typename _tcI0::addr>>> {
        return go_impl(go_impl, ds, bs0);
      };
      return EOU_monad::template bind<
          List<Dv<typename _tcI0::tag, typename _tcI0::addr>>,
          Dv<typename _tcI0::tag, typename _tcI0::addr>>(
          go(List<Nat>::cons(a01, List<Nat>::nil()), a10_value),
          [](const List<Dv<typename _tcI0::tag, typename _tcI0::addr>> &r) {
            return EOU_monad::template ret<
                Dv<typename _tcI0::tag, typename _tcI0::addr>>(
                Dv<typename _tcI0::tag, typename _tcI0::addr>::dnum(
                    r.length()));
          });
    }
  }
}

struct natParams {
  using tag = bool;
  using addr = Nat;

  constexpr static bool t0() { return true; }

  static Nat zero() { return Nat::o(); }
};

static_assert(Params<natParams>);

struct BindContinuationBinderFieldOrder {
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
typename _tcI0::template m<T3> Monad0::bind(typename _tcI0::template m<T2> x,
                                            F1 &&x0) {
  return _tcI0::template bind<T2, T3>(std::move(x), x0);
}

#endif // INCLUDED_BIND_CONTINUATION_BINDER_FIELD_ORDER
