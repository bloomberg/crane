#ifndef INCLUDED_HANDLER_COMBINATOR_FAMILY
#define INCLUDED_HANDLER_COMBINATOR_FAMILY

#include "crane_fn.h"
#include "fn.h"
#include "lazy.h"
#include "obj.h"
#include <any>
#include <atomic>
#include <memory>
#include <stdexcept>
#include <type_traits>
#include <utility>
#include <variant>

struct Empty_set;
struct Nat;
template <typename E, typename R, typename itree> struct ItreeF;
template <typename E, typename R> struct Itree;
template <typename E1, typename E2, typename X> struct Sum1;

struct Empty_set {
  Empty_set() = delete;
};

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
  Nat(Nat &&) noexcept = default;
  Nat &operator=(Nat &&) noexcept = default;

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  bool eqb(const Nat &m) const {
    const Nat *_loop_self = this;
    const Nat *_loop_m = &m;
    while (true) {
      auto &&_sv = *_loop_self;
      if (std::holds_alternative<typename Nat::O>(_sv.v())) {
        if (std::holds_alternative<typename Nat::O>(_loop_m->v())) {
          return true;
        } else {
          return false;
        }
      } else {
        const auto &[a0] = std::get<typename Nat::S>(_sv.v());
        if (std::holds_alternative<typename Nat::O>(_loop_m->v())) {
          return false;
        } else {
          const auto &[a00] = std::get<typename Nat::S>(_loop_m->v());
          _loop_self = crane_raw(a0);
          _loop_m = crane_raw(a00);
        }
      }
    }
  }
};

struct Monads {
  template <typename s, template <typename> class m, typename a>
  using stateT = crane::fn<m<std::pair<s, a>>(s)>;
};

template <typename obj, typename c> using Id_ = crane::fn<c(obj)>;
template <typename obj, typename c>
using Cat = crane::fn<c(obj, obj, obj, c, c)>;
template <typename obj, typename c> using Inl = crane::fn<c(obj, obj)>;
template <typename obj, typename c> using ReSum = c;

struct CategoryOps {
  template <typename T1, typename T2>
  static T2 id_(std::type_identity_t<Id_<T1, T2>> id_0, T1 x0_);
  template <typename T1, typename T2>
  static T2 cat(std::type_identity_t<Cat<T1, T2>> cat0, const T1 &x0_,
                const T1 &x1_, const T1 &x2_, const T2 &x3_, T2 x4_);
  template <typename T1, typename T2, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, T1 &, T1 &>
  static T2 inl_(F0 &&_x, std::type_identity_t<Inl<T1, T2>> inl, const T1 &x0_,
                 T1 x1_);
  template <typename T1, typename T2>
  static T2 resum(const T1 &_x, const T1 &_x0, T2 reSum);
  template <typename T1, typename T2>
  static ReSum<T1, T2> ReSum_id(std::type_identity_t<Id_<T1, T2>> x0_,
                                const T1 &x1_);
  template <typename T1, typename T2, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, T1 &, T1 &>
  static ReSum<T1, T2> ReSum_inl(F0 &&bif, std::type_identity_t<Cat<T1, T2>> h0,
                                 std::type_identity_t<Inl<T1, T2>> h2,
                                 const T1 &a, const T1 &b, const T1 &c,
                                 const T2 &h4);
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

  template <typename _U0, typename _U1, typename _U2>
  ItreeF(const ItreeF<_U0, _U1, _U2> &_other)
      : v_([&]() -> variant_t {
          if (std::holds_alternative<typename ItreeF<_U0, _U1, _U2>::RetF>(
                  _other.v())) {
            const auto &[r] =
                std::get<typename ItreeF<_U0, _U1, _U2>::RetF>(_other.v());
            return RetF{[&]() -> R {
              if constexpr (crane_convertible<R, const _U1 &>) {
                return crane_convert<R>(r);
              } else {
                throw std::logic_error("unreachable: inactive constructor "
                                       "field at this instantiation");
              }
            }()};
          } else {
            if (std::holds_alternative<typename ItreeF<_U0, _U1, _U2>::TauF>(
                    _other.v())) {
              const auto &[t] =
                  std::get<typename ItreeF<_U0, _U1, _U2>::TauF>(_other.v());
              return TauF{[&]() -> itree {
                if constexpr (crane_convertible<itree, const _U2 &>) {
                  return crane_convert<itree>(t);
                } else {
                  throw std::logic_error("unreachable: inactive constructor "
                                         "field at this instantiation");
                }
              }()};
            } else {
              const auto &[x, e] =
                  std::get<typename ItreeF<_U0, _U1, _U2>::VisF>(_other.v());
              return VisF{[&]() -> E {
                            if constexpr (crane_convertible<E, const _U0 &>) {
                              return crane_convert<E>(x);
                            } else {
                              throw std::logic_error(
                                  "unreachable: inactive constructor field at "
                                  "this instantiation");
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
  template <typename _S0 = Itree<E, R>> struct Go_ {
    ItreeF<E, R, _S0> _observe;
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

  template <typename _U0, typename _U1>
  Itree(const Itree<_U0, _U1> &_other)
      : lazy_v_(crane::lazy<variant_t>::converted_from(
            _other.lazy_cell(), [=]() -> variant_t {
              const auto &[_observe] =
                  std::get<typename Itree<_U0, _U1>::Go>(_other.v());
              return Go{crane_convert<ItreeF<E, R, Itree<E, R>>>(_observe)};
            })) {}

  explicit Itree(crane::fn<variant_t()> _thunk)
      : lazy_v_(crane::lazy<variant_t>(std::move(_thunk))) {}

  static Itree<E, R> go(ItreeF<E, R, Itree<E, R>> _observe) {
    return Itree<E, R>(Go{std::move(_observe)});
  }

  explicit Itree(crane::lazy<variant_t> _cell) : lazy_v_(std::move(_cell)) {}

  template <typename F> static Itree<E, R> lazy_(F &&thunk) {
    return Itree<E, R>(
        crane::lazy<variant_t>::delegate(std::forward<F>(thunk)));
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
  subst(std::type_identity_t<crane::fn<Itree<T1, T3>(T2)>> k, Itree<T1, T2> u) {
    auto &&_sv = u.observe();
    if (std::holds_alternative<typename ItreeF<T1, T2, Itree<T1, T2>>::RetF>(
            _sv.v())) {
      const auto &[r0] =
          std::get<typename ItreeF<T1, T2, Itree<T1, T2>>::RetF>(_sv.v());
      return k(r0);
    } else if (std::holds_alternative<
                   typename ItreeF<T1, T2, Itree<T1, T2>>::TauF>(_sv.v())) {
      const auto &[t0] =
          std::get<typename ItreeF<T1, T2, Itree<T1, T2>>::TauF>(_sv.v());
      return Itree<T1, T3>::lazy_([=]() -> Itree<T1, T3> {
        return Itree<T1, T3>::go(
            ItreeF<T1, T3, Itree<T1, T3>>::tauf(subst<T1, T2, T3>(k, t0)));
      });
    } else {
      const auto &[x, e0] =
          std::get<typename ItreeF<T1, T2, Itree<T1, T2>>::VisF>(_sv.v());
      return Itree<T1, T3>::go(ItreeF<T1, T3, Itree<T1, T3>>::visf(
          x, crane::fn<Itree<T1, T3>(crane::obj)>(
                 [=](const crane::obj &x0) -> Itree<T1, T3> {
                   return subst<T1, T2, T3>(k, crane_call_erased(e0, x0));
                 })));
    }
  }

  template <typename T1, typename T2, typename T3>
  static Itree<T1, T3>
  bind(Itree<T1, T2> u, std::type_identity_t<crane::fn<Itree<T1, T3>(T2)>> k) {
    return subst<T1, T2, T3>(std::move(k), u);
  }

  template <typename T1, typename T2>
  static Itree<T1, T2> trigger(crane::rebind_t<T1, T2> e) {
    return Itree<T1, T2>::go(ItreeF<T1, T2, Itree<T1, T2>>::visf(
        std::move(e),
        crane::fn<Itree<T1, T2>(crane::obj)>(
            [](const crane::obj &x) -> Itree<T1, T2> {
              return Itree<T1, T2>::go(
                  ItreeF<T1, T2, Itree<T1, T2>>::retf(crane_any_cast<T2>(x)));
            })));
  }
};

template <typename E1, typename E2, typename X> struct Sum1 {
  // TYPES
  struct Inl1 {
    crane::rebind_t<E1, X> a0;
  };

  struct Inr1 {
    crane::rebind_t<E2, X> a0;
  };

  using variant_t = std::variant<Inl1, Inr1>;
  using crane_family_tag = void;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  Sum1() {}

  explicit Sum1(Inl1 _v) : v_(std::move(_v)) {}

  explicit Sum1(Inr1 _v) : v_(std::move(_v)) {}

  template <typename _U0, typename _U1, typename _U2>
  Sum1(const Sum1<_U0, _U1, _U2> &_other)
      : v_([&]() -> variant_t {
          if (std::holds_alternative<typename Sum1<_U0, _U1, _U2>::Inl1>(
                  _other.v())) {
            const auto &[a0] =
                std::get<typename Sum1<_U0, _U1, _U2>::Inl1>(_other.v());
            return Inl1{[&]() -> E1 {
              if constexpr (crane_convertible<E1, const _U0 &>) {
                return crane_convert<E1>(a0);
              } else {
                throw std::logic_error("unreachable: inactive constructor "
                                       "field at this instantiation");
              }
            }()};
          } else {
            const auto &[a0] =
                std::get<typename Sum1<_U0, _U1, _U2>::Inr1>(_other.v());
            return Inr1{[&]() -> E2 {
              if constexpr (crane_convertible<E2, const _U1 &>) {
                return crane_convert<E2>(a0);
              } else {
                throw std::logic_error("unreachable: inactive constructor "
                                       "field at this instantiation");
              }
            }()};
          }
        }()) {}

  static Sum1<E1, E2, X> inl1(crane::rebind_t<E1, X> a0) {
    return Sum1<E1, E2, X>(Inl1{std::move(a0)});
  }

  static Sum1<E1, E2, X> inr1(crane::rebind_t<E2, X> a0) {
    return Sum1<E1, E2, X>(Inr1{std::move(a0)});
  }

  // MANIPULATORS
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

template <typename e, typename f> using IFun = crane::fn<f(e)>;

struct Function {
  static crane::obj Id_IFun(crane::obj e);
  static crane::obj Cat_IFun(IFun<crane::obj, crane::obj> f1,
                             IFun<crane::obj, crane::obj> f2, crane::obj e);
  static crane::obj Inl_sum1(crane::obj x);
};

struct Subevent {
  template <typename T1, typename T2, typename T3>
  static crane::rebind_t<T2, T3>
  subevent(ReSum<crane::obj, IFun<crane::obj, crane::obj>> h,
           crane::rebind_t<T1, T3> x);
};

template <typename _P0> struct _crane_carrier_tch {
  template <typename _CraneTcArg> using c = Itree<_P0, _CraneTcArg>;
};

struct HandlerCombinatorFamily {
  enum class MemE { LOAD };
  enum class IntrE { INTR };
  enum class FailE { FAIL };

  struct noE {
    noE() = delete;
  };

  template <typename x> using BotE = Sum1<FailE, noE, x>;

  template <typename T1, typename T2>
  static Monads::template stateT<Nat, _crane_carrier_tch<T1>::template c, T2>
  memM_interp(ReSum<crane::obj, IFun<crane::obj, crane::obj>> h, MemE) {
    return [=](const Nat &s) -> Itree<T1, std::pair<Nat, T2>> {
      if (s.eqb(Nat::o())) {
        return ITree::template bind<T1, Empty_set, std::pair<Nat, Nat>>(
            ITree::template trigger<T1, Empty_set>(
                Subevent::template subevent<FailE, T1, Empty_set>(h,
                                                                  FailE::FAIL)),
            [](Empty_set) -> Itree<T1, std::pair<Nat, Nat>> {
              throw std::logic_error("absurd case");
            });
      } else {
        return Itree<T1, std::pair<Nat, T2>>::go(
            ItreeF<T1, std::pair<Nat, T2>, Itree<T1, std::pair<Nat, T2>>>::retf(
                std::make_pair(s, s)));
      }
    };
  }

  template <typename T1, typename T2, typename F0>
  static Monads::template stateT<Nat, _crane_carrier_tch<T1>::template c, T2>
  handle_intrinsic(F0 &&h, IntrE) {
    return h(MemE::LOAD);
  }

  template <typename _CraneTcArg>
  using _crane_carrier_tc_e3be5dd3911106e2 =
      Itree<BotE<crane::obj>, _CraneTcArg>;

  template <typename T1>
  static Monads::template stateT<Nat, _crane_carrier_tc_e3be5dd3911106e2, T1>
  on_mem(std::type_identity_t<
         Monads::template stateT<Nat, _crane_carrier_tc_e3be5dd3911106e2, T1>>
             f) {
    return f;
  }

  template <typename T1>
  static Monads::template stateT<Nat, _crane_carrier_tc_e3be5dd3911106e2, T1>
  fused_intrinsic(IntrE e) {
    return on_mem<T1>(handle_intrinsic<BotE<crane::obj>, T1>(
        []() {
          return [](MemE _x0)
                     -> Monads::template stateT<
                         Nat, _crane_carrier_tc_e3be5dd3911106e2, crane::obj> {
            return memM_interp<BotE<crane::obj>, crane::obj>(
                CategoryOps::template ReSum_inl<
                    crane::obj, crane::fn<crane::obj(crane::obj)>>(
                    [](const auto &, const auto &) { return crane::obj(); },
                    [](crane::obj, crane::obj, crane::obj, const auto &x,
                       crane::fn<crane::obj(crane::obj)> x0) {
                      return [=](crane::obj _x0) -> crane::obj {
                        return Function::Cat_IFun(
                            x,
                            crane::any_cast<IFun<crane::obj, crane::obj>>(x0),
                            _x0);
                      };
                    },
                    [](crane::obj, crane::obj) {
                      return crane_erase_fn<crane::obj>(Function::Inl_sum1);
                    },
                    crane::obj(), crane::obj(), crane::obj(),
                    CategoryOps::template ReSum_id<
                        crane::obj, crane::fn<crane::obj(crane::obj)>>(
                        [](crane::obj) {
                          return crane_erase_fn<crane::obj>(Function::Id_IFun);
                        },
                        crane::obj())),
                _x0);
          };
        }(),
        e));
  }

  static inline const Itree<BotE<crane::obj>, std::pair<Nat, Nat>> out =
      crane::any_cast<Itree<BotE<crane::obj>, std::pair<Nat, Nat>>>(
          fused_intrinsic<Nat>(IntrE::INTR)(
              Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::o())))))));
  static inline const bool is_five = []() {
    auto &&_sv = out.observe();
    if (std::holds_alternative<typename ItreeF<
            Sum1<FailE, noE, crane::obj>, std::pair<Nat, Nat>,
            Itree<Sum1<FailE, noE, crane::obj>, std::pair<Nat, Nat>>>::RetF>(
            _sv.v())) {
      const auto &[r0] = std::get<typename ItreeF<
          Sum1<FailE, noE, crane::obj>, std::pair<Nat, Nat>,
          Itree<Sum1<FailE, noE, crane::obj>, std::pair<Nat, Nat>>>::RetF>(
          _sv.v());
      const auto &[_x, n] = r0;
      return n.eqb(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::o()))))));
    } else {
      return false;
    }
  }();
};

template <typename T1, typename T2>
T2 CategoryOps::id_(std::type_identity_t<Id_<T1, T2>> id_0, T1 x0_) {
  return id_0(std::move(x0_));
}

template <typename T1, typename T2>
T2 CategoryOps::cat(std::type_identity_t<Cat<T1, T2>> cat0, const T1 &x0_,
                    const T1 &x1_, const T1 &x2_, const T2 &x3_, T2 x4_) {
  return cat0(x0_, x1_, x2_, x3_, std::move(x4_));
}

template <typename T1, typename T2, typename F0>
  requires std::is_invocable_r_v<T1, F0 &, T1 &, T1 &>
T2 CategoryOps::inl_(F0 &&, std::type_identity_t<Inl<T1, T2>> inl,
                     const T1 &x0_, T1 x1_) {
  return inl(x0_, std::move(x1_));
}

template <typename T1, typename T2>
T2 CategoryOps::resum(const T1 &, const T1 &, T2 reSum) {
  return reSum;
}

template <typename T1, typename T2>
ReSum<T1, T2> CategoryOps::ReSum_id(std::type_identity_t<Id_<T1, T2>> x0_,
                                    const T1 &x1_) {
  return CategoryOps::template id_<T1, T2>(std::move(x0_), x1_);
}

template <typename T1, typename T2, typename F0>
  requires std::is_invocable_r_v<T1, F0 &, T1 &, T1 &>
ReSum<T1, T2>
CategoryOps::ReSum_inl(F0 &&bif, std::type_identity_t<Cat<T1, T2>> h0,
                       std::type_identity_t<Inl<T1, T2>> h2, const T1 &a,
                       const T1 &b, const T1 &c, const T2 &h4) {
  return CategoryOps::template cat<T1, T2>(
      std::move(h0), a, b, bif(b, c),
      CategoryOps::template resum<T1, T2>(a, b, h4),
      CategoryOps::template inl_<T1, T2>(bif, std::move(h2), b, c));
}

template <typename T1, typename T2, typename T3>
crane::rebind_t<T2, T3>
Subevent::subevent(ReSum<crane::obj, IFun<crane::obj, crane::obj>> h,
                   crane::rebind_t<T1, T3> x) {
  return crane_any_cast<crane::rebind_t<T2, T3>>(
      CategoryOps::resum(crane::obj(), crane::obj(), h)(std::move(x)));
}

#endif // INCLUDED_HANDLER_COMBINATOR_FAMILY
