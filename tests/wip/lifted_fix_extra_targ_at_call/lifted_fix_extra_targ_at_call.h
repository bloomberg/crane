#ifndef INCLUDED_LIFTED_FIX_EXTRA_TARG_AT_CALL
#define INCLUDED_LIFTED_FIX_EXTRA_TARG_AT_CALL

#include "crane_fn.h"
#include "small_vector.h"
#include <any>
#include <atomic>
#include <concepts>
#include <functional>
#include <memory>
#include <optional>
#include <stdexcept>
#include <type_traits>
#include <utility>
#include <variant>

struct Monad_option;
struct Nat;
template <typename A> struct List;
struct Dtyp;
template <typename ptr> struct Dvalue;
struct natParams;
using ptr = std::any;
template <typename I>
concept Functor = requires {
  typename I::template F<std::any>;
  {
    I::template fmap<std::any, std::any>(
        std::declval<std::function<std::any(std::any)>>(),
        std::declval<typename I::template F<std::any>>())
  } -> std::convertible_to<typename I::template F<std::any>>;
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
template <typename
I>concept Params = requires {
  typename I::ptr;
} && (requires {
  { I::nullp() } -> std::convertible_to<typename I::ptr>;
} || requires {
  { I::nullp } -> std::convertible_to<typename I::ptr>;
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
};

struct Functor0 {
  template <Functor _tcI0, typename T2, typename T3, typename F0>
    requires std::is_invocable_r_v<T3, F0 &, T2 &>
  static typename _tcI0::template F<T3> fmap(F0 &&x,
                                             typename _tcI0::template F<T2> x0);
};

struct Monad0 {
  template <Monad _tcI0, typename T2>
  static typename _tcI0::template m<T2> ret(const T2 &x);
  template <Monad _tcI0, typename T2, typename T3, typename F1>
    requires std::is_invocable_r_v<typename _tcI0::template m<T3>, F1 &, T2 &>
  static typename _tcI0::template m<T3> bind(typename _tcI0::template m<T2> x,
                                             F1 &&x0);
  template <Monad _tcI0, typename T2, typename T3, typename F0>
    requires std::is_invocable_r_v<T3, F0 &, T2 &>
  static typename _tcI0::template m<T3> liftM(F0 &&f,
                                              typename _tcI0::template m<T2> x);
};

template <Monad _tcI0> struct Functor_Monad {
  template <typename _A0> using m = typename _tcI0::template m<_A0>;
  template <typename _A0> using F = typename _tcI0::template m<_A0>;

  template <typename _A0, typename _A1>
  static typename _tcI0::template m<_A1>
  fmap(std::function<_A1(_A0)> a0, typename _tcI0::template m<_A0> a1) {
    return Monad0::template liftM<_tcI0, _A0, _A1>(std::move(a0),
                                                   std::move(a1));
  }
};

struct Monad_option {
  template <typename _A0> using m = std::optional<_A0>;

  template <typename _A0> static std::optional<_A0> ret(_A0 x) {
    return std::make_optional<_A0>(x);
  }

  template <typename _A0, typename _A1>
  static std::optional<_A1> bind(std::optional<_A0> c1,
                                 std::function<std::optional<_A1>(_A0)> c2) {
    if (c1.has_value()) {
      const _A0 &v = *c1;
      return c2(v);
    } else {
      return std::optional<_A1>();
    }
  }
};

static_assert(Monad<Monad_option>);

struct Dtyp {
  // TYPES
  struct DLeaf {};

  struct DStruct {
    std::shared_ptr<List<Dtyp>> a0;
  };

  using variant_t = std::variant<DLeaf, DStruct>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  Dtyp() {}

  explicit Dtyp(DLeaf _v) : v_(_v) {}

  explicit Dtyp(DStruct _v) : v_(std::move(_v)) {}

  static Dtyp dleaf() { return Dtyp(DLeaf{}); }

  static Dtyp dstruct(List<Dtyp> a0) {
    return Dtyp(DStruct{std::make_shared<List<Dtyp>>(std::move(a0))});
  }

  // MANIPULATORS
  ~Dtyp() {
    crane::small_vector<std::shared_ptr<Dtyp>> _stack = {};
    auto _drain = [&](variant_t &_v) {
      if (auto *_alt = std::get_if<DStruct>(&_v)) {
        if (_alt->a0 && _alt->a0.use_count() == 1) {
          std::atomic_thread_fence(std::memory_order_acquire);
          auto _lp = _alt->a0.get();
          while (std::holds_alternative<typename List<Dtyp>::Cons>(_lp->v())) {
            auto &_lc = std::get<typename List<Dtyp>::Cons>(_lp->v_mut());
            _stack.push_back(std::make_shared<Dtyp>(std::move(_lc.a)));
            if (_lc.l && _lc.l.use_count() == 1) {
              std::atomic_thread_fence(std::memory_order_acquire);
              _lp = _lc.l.get();
            } else {
              break;
            }
          }
          _alt->a0.reset();
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

  Dtyp(const Dtyp &) = default;
  Dtyp &operator=(const Dtyp &) = default;
  Dtyp(Dtyp &&) noexcept = default;
  Dtyp &operator=(Dtyp &&) noexcept = default;

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

template <typename ptr> struct Dvalue {
  // TYPES
  struct DV0 {
    ptr a0;
  };

  struct DVS {
    std::shared_ptr<List<Dvalue<ptr>>> a0;
  };

  using variant_t = std::variant<DV0, DVS>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  Dvalue() {}

  explicit Dvalue(DV0 _v) : v_(std::move(_v)) {}

  explicit Dvalue(DVS _v) : v_(std::move(_v)) {}

  template <typename _U> Dvalue(const Dvalue<_U> &_other) {
    if (std::holds_alternative<typename Dvalue<_U>::DV0>(_other.v())) {
      const auto &[a0] = std::get<typename Dvalue<_U>::DV0>(_other.v());
      this->v_ = DV0{a0};
    } else {
      const auto &[a0] = std::get<typename Dvalue<_U>::DVS>(_other.v());
      this->v_ = DVS{a0};
    }
  }

  static Dvalue<ptr> dv0(ptr a0) { return Dvalue<ptr>(DV0{std::move(a0)}); }

  static Dvalue<ptr> dvs(List<Dvalue<ptr>> a0) {
    return Dvalue<ptr>(DVS{std::make_shared<List<Dvalue<ptr>>>(std::move(a0))});
  }

  // MANIPULATORS
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

template <Params _tcI0>
auto _to_dvalue_list_to_dvalue(const std::optional<Nat> pad) {
  auto go_impl = [=](auto &_self_go, Nat offset, List<Dtyp> dts,
                     List<Nat> dbs0) mutable
      -> std::optional<List<Dvalue<typename _tcI0::ptr>>> {
    if (std::holds_alternative<typename List<Dtyp>::Nil>(dts.v())) {
      return Monad0::template ret<Monad_option,
                                  List<Dvalue<typename _tcI0::ptr>>>(
          List<Dvalue<typename _tcI0::ptr>>::nil());
    } else {
      const auto &[a0, a1] = std::get<typename List<Dtyp>::Cons>(dts.v());
      const List<Dtyp> &a1_value = *a1;
      Nat padding;
      if (pad.has_value()) {
        const Nat &p = *pad;
        padding = p;
      } else {
        padding = Nat::o();
      }
      return Monad0::template bind<Monad_option, Dvalue<typename _tcI0::ptr>,
                                   List<Dvalue<typename _tcI0::ptr>>>(
          to_dvalue<_tcI0>(dbs0, a0),
          [=](Dvalue<typename _tcI0::ptr> f) mutable {
            return Monad0::template bind<Monad_option,
                                         List<Dvalue<typename _tcI0::ptr>>,
                                         List<Dvalue<typename _tcI0::ptr>>>(
                _self_go(_self_go, offset.add(padding), a1_value, dbs0),
                [=](List<Dvalue<typename _tcI0::ptr>> rest) mutable {
                  return Monad0::template ret<
                      Monad_option, List<Dvalue<typename _tcI0::ptr>>>(
                      List<Dvalue<typename _tcI0::ptr>>::cons(f, rest));
                });
          });
    }
  };
  auto go = [=](Nat offset, List<Dtyp> dts, List<Nat> dbs0) mutable
      -> std::optional<List<Dvalue<typename _tcI0::ptr>>> {
    return go_impl(go_impl, offset, dts, dbs0);
  };
  return go;
}

template <Params _tcI0>
std::optional<Dvalue<typename _tcI0::ptr>> to_dvalue(const List<Nat> &dbs,
                                                     const Dtyp &dt) {
  if (std::holds_alternative<typename Dtyp::DLeaf>(dt.v())) {
    return Monad0::template ret<Monad_option, Dvalue<typename _tcI0::ptr>>(
        Dvalue<typename _tcI0::ptr>::dv0(_tcI0::nullp()));
  } else {
    const auto &[a0] = std::get<typename Dtyp::DStruct>(dt.v());
    const List<Dtyp> &a0_value = *a0;
    return Functor0::template fmap<Functor_Monad<Monad_option>,
                                   List<Dvalue<typename _tcI0::ptr>>,
                                   Dvalue<typename _tcI0::ptr>>(
        [](List<Dvalue<typename _tcI0::ptr>> x) {
          return Dvalue<typename _tcI0::ptr>::dvs(x);
        },
        _to_dvalue_list_to_dvalue<_tcI0>(std::make_optional<Nat>(
            Nat::s(Nat::o())))(Nat::o(), a0_value, dbs));
  }
}

struct natParams {
  using ptr = Nat;

  static Nat nullp() { return Nat::o(); }
};

static_assert(Params<natParams>);

struct LiftedFixExtraTargAtCall {
  static inline const std::optional<Dvalue<typename natParams::ptr>> run =
      to_dvalue<natParams>(
          List<Nat>::cons(
              Nat::s(Nat::o()),
              List<Nat>::cons(Nat::s(Nat::s(Nat::o())), List<Nat>::nil())),
          Dtyp::dstruct(List<Dtyp>::cons(
              Dtyp::dleaf(),
              List<Dtyp>::cons(Dtyp::dleaf(), List<Dtyp>::nil()))));
};

template <Functor _tcI0, typename T2, typename T3, typename F0>
  requires std::is_invocable_r_v<T3, F0 &, T2 &>
typename _tcI0::template F<T3>
Functor0::fmap(F0 &&x, typename _tcI0::template F<T2> x0) {
  return _tcI0::template fmap<T2, T3>(x, std::move(x0));
}

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
  requires std::is_invocable_r_v<T3, F0 &, T2 &>
typename _tcI0::template m<T3> Monad0::liftM(F0 &&f,
                                             typename _tcI0::template m<T2> x) {
  return Monad0::template bind<_tcI0, T2, T3>(
      std::move(x), [=](const T2 &x0) mutable {
        return Monad0::template ret<_tcI0, T3>(f(x0));
      });
}

#endif // INCLUDED_LIFTED_FIX_EXTRA_TARG_AT_CALL
