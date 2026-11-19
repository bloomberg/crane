#pragma once

#include "crane_fn.h"
#include "fn.h"
#include "lazy.h"
#include "obj.h"
#include <atomic>
#include <concepts>
#include <memory>
#include <stdexcept>
#include <type_traits>
#include <utility>
#include <variant>

struct Nat;
template <typename A, typename B> struct Sum;
template <typename A> struct List;
template <typename E, typename R, typename itree> struct ItreeF;
template <typename E, typename R> struct Itree;

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

  static Nat s(crane::shared_child_slot<Nat> a0) { return Nat(S{a0.take()}); }

  // MANIPULATORS
  ~Nat() {
    // Release the children this node alone owns in a loop, not recursively, so
    // a deep value cannot overflow the stack.
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

  template <typename CraneU0, typename CraneU1>
  Sum(const Sum<CraneU0, CraneU1> &_other)
      : v_([&]() -> variant_t {
          if (std::holds_alternative<typename Sum<CraneU0, CraneU1>::Inl>(
                  _other.v())) {
            const auto &[a0] =
                std::get<typename Sum<CraneU0, CraneU1>::Inl>(_other.v());
            return Inl{[&]() -> A {
              if constexpr (crane_convertible<A, const CraneU0 &>) {
                return crane_convert<A>(a0);
              } else {
                throw std::logic_error("unreachable: inactive constructor "
                                       "field at this instantiation");
              }
            }()};
          } else {
            const auto &[a0] =
                std::get<typename Sum<CraneU0, CraneU1>::Inr>(_other.v());
            return Inr{[&]() -> B {
              if constexpr (crane_convertible<B, const CraneU1 &>) {
                return crane_convert<B>(a0);
              } else {
                throw std::logic_error("unreachable: inactive constructor "
                                       "field at this instantiation");
              }
            }()};
          }
        }()) {}

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

  static List<A> cons(A a, crane::shared_child_slot<List<A>> l) {
    return List<A>(Cons{std::move(a), l.take()});
  }

  // MANIPULATORS
  ~List() {
    // Release the children this node alone owns in a loop, not recursively, so
    // a deep value cannot overflow the stack.
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
};

template <typename E, typename R, typename itree> struct ItreeF {
  // TYPES
  struct RetF {
    R r;
  };

  struct TauF {
    itree t;
  };

  struct VisF {
    E x;
    crane::fn<itree(crane::obj)> e;
  };

  using variant_t = std::variant<RetF, TauF, VisF>;
  using crane_family_tag = void;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  ItreeF() {}

  explicit ItreeF(RetF _v) : v_(std::move(_v)) {}

  explicit ItreeF(TauF _v) : v_(std::move(_v)) {}

  explicit ItreeF(VisF _v) : v_(std::move(_v)) {}

  template <typename CraneU0, typename CraneU1, typename CraneU2>
  ItreeF(const ItreeF<CraneU0, CraneU1, CraneU2> &_other)
      : v_([&]() -> variant_t {
          if (std::holds_alternative<
                  typename ItreeF<CraneU0, CraneU1, CraneU2>::RetF>(_other.v())) {
            const auto &[r] =
                std::get<typename ItreeF<CraneU0, CraneU1, CraneU2>::RetF>(
                    _other.v());
            return RetF{[&]() -> R {
              if constexpr (crane_convertible<R, const CraneU1 &>) {
                return crane_convert<R>(r);
              } else {
                throw std::logic_error("unreachable: inactive constructor "
                                       "field at this instantiation");
              }
            }()};
          } else {
            if (std::holds_alternative<
                    typename ItreeF<CraneU0, CraneU1, CraneU2>::TauF>(
                    _other.v())) {
              const auto &[t] =
                  std::get<typename ItreeF<CraneU0, CraneU1, CraneU2>::TauF>(
                      _other.v());
              return TauF{[&]() -> itree {
                if constexpr (crane_convertible<itree, const CraneU2 &>) {
                  return crane_convert<itree>(t);
                } else {
                  throw std::logic_error("unreachable: inactive constructor "
                                         "field at this instantiation");
                }
              }()};
            } else {
              const auto &[x, e] =
                  std::get<typename ItreeF<CraneU0, CraneU1, CraneU2>::VisF>(
                      _other.v());
              return VisF{
                  [&]() -> E {
                    if constexpr (crane_convertible<E, const CraneU0 &>) {
                      return crane_convert<E>(x);
                    } else {
                      throw std::logic_error("unreachable: inactive "
                                             "constructor field at this "
                                             "instantiation");
                    }
                  }(),
                  crane_convert<crane::fn<itree(crane::obj)>>(e)};
            }
          }
        }()) {}

  static ItreeF<E, R, itree> retf(R r) {
    return ItreeF<E, R, itree>(RetF{std::move(r)});
  }

  static ItreeF<E, R, itree> tauf(itree t) {
    return ItreeF<E, R, itree>(TauF{std::move(t)});
  }

  static ItreeF<E, R, itree> visf(E x, crane::fn<itree(crane::obj)> e) {
    return ItreeF<E, R, itree>(VisF{std::move(x), std::move(e)});
  }

  // MANIPULATORS
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

template <typename E, typename R> struct Itree {
  // TYPES
  template <typename CraneS0 = Itree<E, R>> struct Go_ {
    ItreeF<E, R, CraneS0> _observe;
  };

  using Go = Go_<>;
  using variant_t = std::variant<Go>;
  using crane_family_tag = void;

private:
  // DATA
  crane::lazy<variant_t> lazy_v_;

public:
  // CREATORS
  Itree() {}

  explicit Itree(Go _v)
      : lazy_v_(crane::lazy<variant_t>(variant_t(std::move(_v)))) {}

  template <typename CraneU0, typename CraneU1>
  Itree(const Itree<CraneU0, CraneU1> &_other)
      : lazy_v_(crane::lazy<variant_t>::converted_from(
      _other.lazy_cell(), [=]() -> variant_t {
        const auto &[_observe] =
            std::get<typename Itree<CraneU0, CraneU1>::Go>(_other.v());
        return Go{crane_convert<ItreeF<E, R, Itree<E, R>>>(_observe)};
      })) {}

  explicit Itree(crane::fn<variant_t()> _thunk)
      : lazy_v_(crane::lazy<variant_t>(std::move(_thunk))) {}

  static Itree<E, R> go(ItreeF<E, R, Itree<E, R>> _observe) {
    return Itree<E, R>(crane::lazy<variant_t>(
        std::in_place, std::in_place_index<0>, std::move(_observe)));
  }

  explicit Itree(crane::lazy<variant_t> _cell) : lazy_v_(std::move(_cell)) {}

  template <typename F> static Itree<E, R> lazy_(F &&thunk) {
    return Itree<E, R>(crane::lazy<variant_t>::delegate(std::forward<F>(thunk)));
  }

  // ACCESSORS
  const variant_t &v() const { return lazy_v_.force(); }

  const crane::lazy<variant_t> &lazy_cell() const { return lazy_v_; }

  const ItreeF<E, R, Itree<E, R>> &observe() const & {
    const auto &[_observe] = std::get<typename Itree<E, R>::Go>(this->v());
    return _observe;
  }

  ItreeF<E, R, Itree<E, R>> observe() const && {
    const auto &[_observe] = std::get<typename Itree<E, R>::Go>(this->v());
    return _observe;
  }
};

struct ITree {
  template <typename T1, typename T2, typename T3>
  static Itree<T1, T3>
  subst(std::type_identity_t<crane::fn<Itree<T1, T3>(T2)>> k,
        const Itree<T1, T2> &u) {
    auto &&_sv = u.observe();
    if (std::holds_alternative<typename ItreeF<T1, T2, Itree<T1, T2>>::RetF>(
            _sv.v())) {
      const auto &[r0] =
          std::get<typename ItreeF<T1, T2, Itree<T1, T2>>::RetF>(_sv.v());
      return k(r0);
    } else if (
        std::holds_alternative<typename ItreeF<T1, T2, Itree<T1, T2>>::TauF>(
            _sv.v())) {
      const auto &[t0] =
          std::get<typename ItreeF<T1, T2, Itree<T1, T2>>::TauF>(_sv.v());
      return Itree<T1, T3>::lazy_(
          [=, k = std::move(k)]() mutable -> typename Itree<T1,
                                                            T3>::Go {
            return {ItreeF<T1, T3, Itree<T1, T3>>::tauf(
                subst<T1, T2, T3>(std::move(k), t0))};
          });
    } else {
      const auto &[x, e0] =
          std::get<typename ItreeF<T1, T2, Itree<T1, T2>>::VisF>(_sv.v());
      return Itree<T1, T3>::go(ItreeF<T1, T3, Itree<T1, T3>>::visf(
          x,
          crane::fn<Itree<T1, T3>(crane::obj)>([=, e0 = e0, k = std::move(k)](
              const crane::obj &x0)
                                                    -> Itree<T1,
                                                             T3> {
            return subst<T1, T2, T3>(k, crane_call_erased(e0, x0));
          })));
    }
  }

  template <typename T1, typename T2, typename T3>
  static Itree<T1, T3>
  bind(const Itree<T1, T2> &u,
       std::type_identity_t<crane::fn<Itree<T1, T3>(T2)>> k) {
    return subst<T1, T2, T3>(std::move(k), u);
  }

  template <typename T1, typename T2, typename T3>
  static Itree<T1, T3> map(const std::type_identity_t<crane::fn<T3(T2)>> &f,
                           const Itree<T1, T2> &t) {
    return bind<T1, T2, T3>(t, [=, f = f](const T2 &x) {
      return Itree<T1, T3>::go(ItreeF<T1, T3, Itree<T1, T3>>::retf(f(x)));
    });
  }
};

template <typename I>
concept Params = requires {
  typename I::ptr;
  { I::mkp(std::declval<Nat>()) } -> std::convertible_to<typename I::ptr>;
};
template <typename I>
concept MS = requires {
  typename I::state;
} && (requires {
  {
    I::init()
  }
  -> std::convertible_to<typename I::state>;
} || requires {
  {
    I::init
  }
  -> std::convertible_to<typename I::state>;
});
template <typename I>
concept MP = requires {
  typename I::mm;
  { I::foo() } -> std::convertible_to<Nat>;
};

struct SubclassTypeProjectionAlias {
  using ptr = crane::obj;
  enum class Err { E1, E2 };
  using state = crane::obj;

  template <typename ptr> struct State {
    List<ptr> mem;
  };

  template <Params _tcI0> struct msV {
    using ptr = typename _tcI0::ptr;
    using state = State<typename _tcI0::ptr>;

    static State<typename _tcI0::ptr> init() {
      return State<typename _tcI0::ptr>{List<typename _tcI0::ptr>::nil()};
    }
  };

  template <Params _tcI0> struct mpV {
    using mm = msV<_tcI0>;
    using ptr = typename _tcI0::ptr;
    using state = typename mm::state;

    static Nat foo() { return Nat::o(); }
  };

  template <typename ptr> struct dv {
    // TYPES
    struct DV0 {
      ptr a0;
    };

    struct DN {
      Nat a0;
    };

    using variant_t = std::variant<DV0, DN>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    dv() {}

    explicit dv(DV0 _v) : v_(std::move(_v)) {}

    explicit dv(DN _v) : v_(std::move(_v)) {}

    template <typename CraneU>
    dv(const dv<CraneU> &_other)
        : v_([&]() -> variant_t {
            if (std::holds_alternative<typename dv<CraneU>::DV0>(_other.v())) {
              const auto &[a0] = std::get<typename dv<CraneU>::DV0>(_other.v());
              return DV0{[&]() -> ptr {
                if constexpr (crane_convertible<ptr, const CraneU &>) {
                  return crane_convert<ptr>(a0);
                } else {
                  throw std::logic_error("unreachable: inactive constructor "
                                         "field at this instantiation");
                }
              }()};
            } else {
              const auto &[a0] = std::get<typename dv<CraneU>::DN>(_other.v());
              return DN{a0};
            }
          }()) {}

    static dv<ptr> dv0(ptr a0) { return dv<ptr>(DV0{std::move(a0)}); }

    static dv<ptr> dn(Nat a0) { return dv<ptr>(DN{std::move(a0)}); }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <Params _tcI0, typename T1, typename F0, typename F1>
    requires std::is_invocable_r_v<T1, F0 &, const typename _tcI0::ptr &> &&
             std::is_invocable_r_v<T1, F1 &, const Nat &>
  static T1 dv_rect(F0 &&f, F1 &&f0, const dv<typename _tcI0::ptr> &d) {
    if (std::holds_alternative<typename dv<typename _tcI0::ptr>::DV0>(d.v())) {
      const auto &[a0] = std::get<typename dv<typename _tcI0::ptr>::DV0>(d.v());
      return f(a0);
    } else {
      const auto &[a0] = std::get<typename dv<typename _tcI0::ptr>::DN>(d.v());
      return f0(a0);
    }
  }

  template <Params _tcI0, typename T1, typename F0, typename F1>
  static T1 dv_rec(F0 &&f, F1 &&f0, const dv<typename _tcI0::ptr> &d) {
    return dv_rect<_tcI0, T1>(f, f0, d);
  }

  template <typename ptr> using FusedS = std::pair<State<ptr>, List<Nat>>;
  template <typename ptr, typename x> using Res = std::pair<FusedS<ptr>, x>;

  template <Params _tcI0>
  static Itree<crane::obj, Res<typename _tcI0::ptr, dv<typename _tcI0::ptr>>>
  interp() {
    return Itree<crane::obj,
                 Res<typename _tcI0::ptr, dv<typename _tcI0::ptr>>>::go(ItreeF<
        crane::obj, std::pair<std::pair<State<typename _tcI0::ptr>, List<Nat>>,
                              dv<typename _tcI0::ptr>>,
        Itree<crane::obj,
              std::pair<std::pair<State<typename _tcI0::ptr>, List<Nat>>,
                        dv<typename _tcI0::ptr>>>>::retf(std::make_pair(
        std::make_pair(mpV<_tcI0>::mm::init(), List<Nat>::nil()),
        dv<typename _tcI0::ptr>::dn(Nat::s(Nat::s(Nat::s(Nat::o())))))));
  }

  template <Params _tcI0>
  static Itree<crane::obj, Sum<Err, dv<typename _tcI0::ptr>>>
  run_program(const Itree<
      crane::obj,
      Sum<Err, std::pair<std::pair<State<typename _tcI0::ptr>, List<Nat>>,
                         dv<typename _tcI0::ptr>>>> &t) {
    return ITree::template bind<
        crane::obj, Sum<Err, Res<typename _tcI0::ptr, dv<typename _tcI0::ptr>>>,
        Sum<Err, dv<typename _tcI0::ptr>>>(
        t,
        [](const Sum<Err,
                     std::pair<std::pair<State<typename _tcI0::ptr>, List<Nat>>,
                               dv<typename _tcI0::ptr>>> &r) {
          return Itree<crane::obj, Sum<Err, dv<typename _tcI0::ptr>>>::go(
              ItreeF<crane::obj, Sum<Err, dv<typename _tcI0::ptr>>,
                     Itree<crane::obj,
                           Sum<Err, dv<typename _tcI0::ptr>>>>::retf([&]() {
                if (std::holds_alternative<
                        typename Sum<
                            Err, std::pair<std::pair<State<typename _tcI0::ptr>,
                                                     List<Nat>>,
                                           dv<typename _tcI0::ptr>>>::Inl>(
                        r.v())) {
                  const auto &[a0] = std::get<typename Sum<
                      Err, std::pair<
                               std::pair<State<typename _tcI0::ptr>, List<Nat>>,
                               dv<typename _tcI0::ptr>>>::Inl>(r.v());
                  return Sum<Err, dv<typename _tcI0::ptr>>::inl(a0);
                } else {
                  const auto &[a0] = std::get<typename Sum<
                      Err, std::pair<
                               std::pair<State<typename _tcI0::ptr>, List<Nat>>,
                               dv<typename _tcI0::ptr>>>::Inr>(r.v());
                  const auto &[_x, d] = a0;
                  return Sum<Err, dv<typename _tcI0::ptr>>::inr(d);
                }
              }()));
        });
  }

  struct natParams {
    using ptr = Nat;

    static Nat mkp(Nat n) { return n; }
  };

  static_assert(Params<natParams>);
  static Itree<crane::obj, Sum<Err, dv<typename natParams::ptr>>> run();
};
