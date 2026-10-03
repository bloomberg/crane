#ifndef INCLUDED_ITREE_INTERP_STATE
#define INCLUDED_ITREE_INTERP_STATE

#include "crane_fn.h"
#include "fn.h"
#include "lazy.h"
#include "obj.h"
#include <any>
#include <atomic>
#include <concepts>
#include <memory>
#include <optional>
#include <stdexcept>
#include <type_traits>
#include <utility>
#include <variant>

struct Nat;
template <typename A, typename B> struct Sum;
template <typename E, typename R, typename itree> struct ItreeF;
template <typename E, typename R> struct Itree;
template <typename T1> struct Functor_itree;
template <typename T1> struct Monad_itree;
template <typename I>
concept Functor = requires {
  typename I::template F<crane::obj>;
  {
    I::template fmap<crane::obj, crane::obj>(
        std::declval<crane::fn<crane::obj(crane::obj)>>(),
        std::declval<typename I::template F<crane::obj>>())
  } -> std::convertible_to<typename I::template F<crane::obj>>;
};
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

  template <typename _U0, typename _U1>
  Sum(const Sum<_U0, _U1> &_other)
      : v_([&]() -> variant_t {
          if (std::holds_alternative<typename Sum<_U0, _U1>::Inl>(_other.v())) {
            const auto &[a0] =
                std::get<typename Sum<_U0, _U1>::Inl>(_other.v());
            return Inl{[&]() -> A {
              if constexpr (crane_convertible<A, const _U0 &>) {
                return crane_convert<A>(a0);
              } else {
                throw std::logic_error("unreachable: inactive constructor "
                                       "field at this instantiation");
              }
            }()};
          } else {
            const auto &[a0] =
                std::get<typename Sum<_U0, _U1>::Inr>(_other.v());
            return Inr{[&]() -> B {
              if constexpr (crane_convertible<B, const _U1 &>) {
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
};

template <typename obj, typename c> using Id_ = crane::fn<c(obj)>;
template <typename obj, typename c> using ReSum = c;

struct CategoryOps {
  template <typename T1, typename T2>
  static T2 id_(std::type_identity_t<Id_<T1, T2>> id_0, T1 x0_);
  template <typename T1, typename T2>
  static T2 resum(const T1 &_x, const T1 &_x0, T2 reSum);
  template <typename T1, typename T2>
  static ReSum<T1, T2> ReSum_id(std::type_identity_t<Id_<T1, T2>> x0_,
                                const T1 &x1_);
};

template <typename e, typename f> using IFun = crane::fn<f(e)>;

struct Function {
  static crane::obj Id_IFun(crane::obj e);
};

struct Monads {
  template <typename s, template <typename> class m, typename a>
  using stateT = crane::fn<m<std::pair<s, a>>(s)>;

  template <Functor _tcI0, typename T1> struct Functor_stateT {
    template <typename _A0>
    using F = crane::fn<typename _tcI0::template F<std::pair<T1, _A0>>(T1)>;

    template <typename _A0, typename _A1>
    static crane::fn<typename _tcI0::template F<std::pair<T1, _A1>>(T1)>
    fmap(crane::fn<_A1(_A0)> f,
         crane::fn<typename _tcI0::template F<std::pair<T1, _A0>>(T1)> run0) {
      return [=](const T1 &s) {
        return Functor0::template fmap<_tcI0, std::pair<T1, _A0>,
                                       std::pair<T1, _A1>>(
            [=](const std::pair<T1, _A0> &sa) {
              return std::make_pair(sa.first, f(sa.second));
            },
            run0(s));
      };
    }
  };

  template <Monad _tcI0, typename T1> struct Monad_stateT {
    template <typename _A0>
    using m = crane::fn<typename _tcI0::template m<std::pair<T1, _A0>>(T1)>;

    template <typename _A0>
    static crane::fn<typename _tcI0::template m<std::pair<T1, _A0>>(T1)>
    ret(_A0 a) {
      return [=](const T1 &s) {
        return Monad0::template ret<_tcI0, std::pair<T1, _A0>>(
            std::make_pair(s, a));
      };
    }

    template <typename _A0, typename _A1>
    static crane::fn<typename _tcI0::template m<std::pair<T1, _A1>>(T1)>
    bind(crane::fn<typename _tcI0::template m<std::pair<T1, _A0>>(T1)> t,
         crane::fn<
             crane::fn<typename _tcI0::template m<std::pair<T1, _A1>>(T1)>(_A0)>
             k) {
      return [=](const T1 &s) {
        return Monad0::template bind<_tcI0, std::pair<T1, _A0>,
                                     std::pair<T1, _A1>>(
            t(s), [=](const std::pair<T1, _A0> &sa) {
              return k(sa.second)(sa.first);
            });
      };
    }
  };
};
template <template <typename> class m>
using MonadIter = crane::fn<m<crane::obj>(
    crane::fn<m<Sum<crane::obj, crane::obj>>(crane::obj)>, crane::obj)>;

template <template <typename> class T1, typename T2, typename T3, typename F1>
T1<T2> iter(std::type_identity_t<MonadIter<T1>> monadIter, F1 &&x,
            const T3 &x0) {
  return crane_container_cast<T1<T2>>(
      monadIter(crane_erase_fn<T1<Sum<crane::obj, crane::obj>>>(x), x0));
}

template <Monad _tcI0, typename T2>
Monads::template stateT<T2, _tcI0::template m, crane::obj> MonadIter_stateT0(
    std::type_identity_t<MonadIter<_tcI0::template m>> aM,
    std::type_identity_t<crane::fn<Monads::template stateT<
        T2, _tcI0::template m, Sum<crane::obj, crane::obj>>(crane::obj)>>
        step,
    crane::obj i) {
  return [=](const T2 &s) {
    return iter<_tcI0::template m, std::pair<T2, crane::obj>,
                std::pair<T2, crane::obj>>(
        aM,
        [=](const std::pair<T2, crane::obj> &si) {
          T2 s0 = si.first;
          auto i0 = si.second;
          return Monad0::template bind<
              _tcI0, std::pair<T2, Sum<crane::obj, crane::obj>>,
              Sum<std::pair<T2, crane::obj>, std::pair<T2, crane::obj>>>(
              step(i0)(s0),
              [](const std::pair<T2, Sum<crane::obj, crane::obj>> &si_) {
                return Monad0::template ret<
                    _tcI0,
                    Sum<std::pair<T2, crane::obj>, std::pair<T2, crane::obj>>>(
                    [&]() {
                      auto &&_sv = si_.second;
                      if (std::holds_alternative<
                              typename Sum<crane::obj, crane::obj>::Inl>(
                              _sv.v())) {
                        const auto &[a0] =
                            std::get<typename Sum<crane::obj, crane::obj>::Inl>(
                                _sv.v());
                        return Sum<std::pair<T2, crane::obj>,
                                   std::pair<T2, crane::obj>>::
                            inl(std::make_pair(si_.first,
                                               crane_any_cast<crane::obj>(a0)));
                      } else {
                        const auto &[a0] =
                            std::get<typename Sum<crane::obj, crane::obj>::Inr>(
                                _sv.v());
                        return Sum<std::pair<T2, crane::obj>,
                                   std::pair<T2, crane::obj>>::
                            inr(std::make_pair(si_.first,
                                               crane_any_cast<crane::obj>(a0)));
                      }
                    }());
              });
        },
        std::make_pair(s, i));
  };
}

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
    return Itree<E, R>(crane::lazy<variant_t>(
        std::in_place, std::in_place_index<0>, std::move(_observe)));
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

  template <typename T1, typename T2, typename T3>
  static Itree<T1, T2>
  iter(std::type_identity_t<crane::fn<Itree<T1, Sum<T3, T2>>(T3)>> step,
       const T3 &i) {
    return bind<T1, Sum<T3, T2>, T2>(
        step(i), [=](const Sum<T3, T2> &lr) -> Itree<T1, T2> {
          if (std::holds_alternative<typename Sum<T3, T2>::Inl>(lr.v())) {
            const auto &[a0] = std::get<typename Sum<T3, T2>::Inl>(lr.v());
            return Itree<T1, T2>::lazy_([=]() -> Itree<T1, T2> {
              return Itree<T1, T2>::go(ItreeF<T1, T2, Itree<T1, T2>>::tauf(
                  iter<T1, T2, T3>(step, a0)));
            });
          } else {
            const auto &[a0] = std::get<typename Sum<T3, T2>::Inr>(lr.v());
            return Itree<T1, T2>::go(ItreeF<T1, T2, Itree<T1, T2>>::retf(a0));
          }
        });
  }

  template <typename T1, typename T2, typename T3>
  static Itree<T1, T3> map(std::type_identity_t<crane::fn<T3(T2)>> f,
                           Itree<T1, T2> t) {
    return bind<T1, T2, T3>(t, [=](const T2 &x) {
      return Itree<T1, T3>::lazy_([=]() -> Itree<T1, T3> {
        return Itree<T1, T3>::go(ItreeF<T1, T3, Itree<T1, T3>>::retf(f(x)));
      });
    });
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

template <typename T1> struct Functor_itree {
  template <typename _A0> using F = Itree<T1, _A0>;

  template <typename _A0, typename _A1>
  static Itree<T1, _A1> fmap(crane::fn<_A1(_A0)> a0, Itree<T1, _A0> a1) {
    return ITree::template map<T1, _A0, _A1>(std::move(a0), a1);
  }
};

template <typename T1> struct Monad_itree {
  template <typename _A0> using m = Itree<T1, _A0>;

  template <typename _A0> static Itree<T1, _A0> ret(_A0 x) {
    return Itree<T1, _A0>::go(
        ItreeF<crane::obj, crane::obj, Itree<crane::obj, crane::obj>>::retf(
            std::move(x)));
  }

  template <typename _A0, typename _A1>
  static Itree<T1, _A1> bind(Itree<T1, _A0> a0,
                             crane::fn<Itree<T1, _A1>(_A0)> a1) {
    return ITree::template bind<T1, _A0, _A1>(a0, std::move(a1));
  }
};

template <typename T1, typename F0>
Itree<T1, crane::obj> MonadIter_itree(F0 &&x0_, crane::obj x1_) {
  return ITree::template iter<T1, crane::obj, crane::obj>(x0_, x1_);
}

struct Subevent {
  template <typename T1, typename T2, typename T3>
  static crane::rebind_t<T2, T3>
  subevent(ReSum<crane::obj, IFun<crane::obj, crane::obj>> h0,
           crane::rebind_t<T1, T3> x);
};

struct Interp {
  template <Monad _tcI0, Functor _tcI1, typename T1, typename T3>
  static typename _tcI0::template m<T3>
  interp(std::type_identity_t<MonadIter<_tcI0::template m>> iM,
         std::type_identity_t<
             crane::fn<typename _tcI0::template m<crane::obj>(T1)>>
             h0,
         Itree<T1, T3> x0_);
};

struct State {
  template <Monad _tcI0, Functor _tcI1, typename T1, typename T3, typename T4>
  static Monads::template stateT<T3, _tcI0::template m, T4> interp_state(
      std::type_identity_t<MonadIter<_tcI0::template m>> iM,
      std::type_identity_t<crane::fn<
          Monads::template stateT<T3, _tcI0::template m, crane::obj>(T1)>>
          h0,
      Itree<T1, T4> x);
};

struct ItreeInterpState {
  enum class GetE { GET };

  struct noE {
    noE() = delete;
  };

  static inline const Itree<GetE, Nat> prog = []() {
    return ITree::template bind<GetE, Nat, Nat>(
        ITree::template trigger<GetE, Nat>(
            Subevent::template subevent<GetE, GetE, Nat>(
                CategoryOps::template ReSum_id<
                    crane::obj, crane::fn<crane::obj(crane::obj)>>(
                    [](crane::obj) {
                      return crane_erase_fn<crane::obj>(Function::Id_IFun);
                    },
                    crane::obj()),
                GetE::GET)),
        [](const Nat &x) {
          return ITree::template bind<GetE, Nat, Nat>(
              ITree::template trigger<GetE, Nat>(
                  Subevent::template subevent<GetE, GetE, Nat>(
                      CategoryOps::template ReSum_id<
                          crane::obj, crane::fn<crane::obj(crane::obj)>>(
                          [](crane::obj) {
                            return crane_erase_fn<crane::obj>(
                                Function::Id_IFun);
                          },
                          crane::obj()),
                      GetE::GET)),
              [=](const Nat &y) {
                return Itree<GetE, Nat>::lazy_([=]() -> Itree<GetE, Nat> {
                  return Itree<GetE, Nat>::go(
                      ItreeF<GetE, Nat, Itree<GetE, Nat>>::retf(x.add(y)));
                });
              });
        });
  }();
  template <typename _CraneTcArg>
  using _crane_carrier_tc_d02fdfd8331afb33 = Itree<noE, _CraneTcArg>;

  template <typename T1>
  static Monads::template stateT<Nat, _crane_carrier_tc_d02fdfd8331afb33, T1>
  h(GetE) {
    return [](const Nat &s) {
      return Itree<noE, std::pair<Nat, T1>>::go(
          ItreeF<noE, std::pair<Nat, T1>, Itree<noE, std::pair<Nat, T1>>>::retf(
              std::make_pair(Nat::s(s), s)));
    };
  }

  static inline const Itree<noE, std::pair<Nat, Nat>> out =
      State::template interp_state<Monad_itree<noE>, Functor_itree<noE>, GetE,
                                   Nat, Nat>(
          [](auto &&_ec0, crane::obj _ec1) {
            return MonadIter_itree<noE>(_ec0, _ec1);
          },
          [](const GetE &a0)
              -> Monads::template stateT<
                  Nat, _crane_carrier_tc_d02fdfd8331afb33, crane::obj> {
            return h<crane::obj>(crane_convert<GetE>(a0));
          },
          prog)(Nat::s(Nat::o()));
  static std::optional<std::pair<Nat, Nat>>
  run(const Nat &fuel, Itree<noE, std::pair<Nat, Nat>> t);
  static inline const bool is_three = []() -> bool {
    auto _cs = []() {
      auto _lit0 = Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(
          Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(
              Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(
                  Nat::s(Nat::s(Nat::s(Nat::o()))))))))))))))))))))))))))))));
      auto _lit1 = Nat::s(Nat::s(
          Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(
              Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(
                  Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(
                      Nat::s(std::move(_lit0)))))))))))))))))))))))))))))));
      auto _lit2 = Nat::s(Nat::s(
          Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(
              Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(
                  Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(
                      Nat::s(std::move(_lit1)))))))))))))))))))))))))))))));
      return run(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(
                     Nat::s(Nat::s(Nat::s(Nat::s(std::move(_lit2))))))))))),
                 out);
    }();
    if (_cs.has_value()) {
      const std::pair<Nat, Nat> &p = *_cs;
      const auto &[_x, n] = p;
      return n.eqb(Nat::s(Nat::s(Nat::s(Nat::o()))));
    } else {
      return false;
    }
  }();
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

template <typename T1, typename T2>
T2 CategoryOps::id_(std::type_identity_t<Id_<T1, T2>> id_0, T1 x0_) {
  return id_0(std::move(x0_));
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

template <typename T1, typename T2, typename T3>
crane::rebind_t<T2, T3>
Subevent::subevent(ReSum<crane::obj, IFun<crane::obj, crane::obj>> h0,
                   crane::rebind_t<T1, T3> x) {
  return crane_any_cast<crane::rebind_t<T2, T3>>(
      CategoryOps::resum(crane::obj(), crane::obj(), h0)(std::move(x)));
}

template <Monad _tcI0, Functor _tcI1, typename T1, typename T3>
typename _tcI0::template m<T3> Interp::interp(
    std::type_identity_t<MonadIter<_tcI0::template m>> iM,
    std::type_identity_t<crane::fn<typename _tcI0::template m<crane::obj>(T1)>>
        h0,
    Itree<T1, T3> x0_) {
  return ::template iter<_tcI0::template m, T3, Itree<T1, T3>>(
      std::move(iM),
      [=](Itree<T1, T3> t) ->
      typename _tcI0::template m<Sum<Itree<T1, T3>, T3>> {
        auto &&_sv = t.observe();
        if (std::holds_alternative<
                typename ItreeF<T1, T3, Itree<T1, T3>>::RetF>(_sv.v())) {
          const auto &[r0] =
              std::get<typename ItreeF<T1, T3, Itree<T1, T3>>::RetF>(_sv.v());
          return Monad0::template ret<_tcI0, Sum<Itree<T1, T3>, T3>>(
              Sum<Itree<T1, T3>, T3>::inr(r0));
        } else if (std::holds_alternative<
                       typename ItreeF<T1, T3, Itree<T1, T3>>::TauF>(_sv.v())) {
          const auto &[t1] =
              std::get<typename ItreeF<T1, T3, Itree<T1, T3>>::TauF>(_sv.v());
          return Monad0::template ret<_tcI0, Sum<Itree<T1, T3>, T3>>(
              Sum<Itree<T1, T3>, T3>::inl(t1));
        } else {
          const auto &[x, e0] =
              std::get<typename ItreeF<T1, T3, Itree<T1, T3>>::VisF>(_sv.v());
          return Functor0::template fmap<_tcI1, crane::obj,
                                         Sum<Itree<T1, T3>, T3>>(
              [=](const auto &x0) {
                return Sum<Itree<T1, T3>, T3>::inl(e0(x0));
              },
              h0(x));
        }
      },
      x0_);
}

template <Monad _tcI0, Functor _tcI1, typename T1, typename T3, typename T4>
Monads::template stateT<T3, _tcI0::template m, T4> State::interp_state(
    std::type_identity_t<MonadIter<_tcI0::template m>> iM,
    std::type_identity_t<crane::fn<
        Monads::template stateT<T3, _tcI0::template m, crane::obj>(T1)>>
        h0,
    Itree<T1, T4> x) {
  return [=](const T3 &x0) {
    return crane_any_cast<typename _tcI0::template m<std::pair<T3, T4>>>(
        Interp::template interp<Monads::template Monad_stateT<_tcI0, T3>,
                                Monads::template Functor_stateT<_tcI1, T3>, T1,
                                T4>(
            [=]() {
              return
                  [=](crane::fn<Monads::template stateT<
                          T3, _tcI0::template m, Sum<crane::obj, crane::obj>>(
                          crane::obj)>
                          _x0,
                      crane::obj _x1)
                      -> Monads::template stateT<T3, _tcI0::template m,
                                                 crane::obj> {
                    return ::template MonadIter_stateT0<_tcI0, T3>(iM, _x0,
                                                                   _x1);
                  };
            }(),
            h0, x)(x0));
  };
}

#endif // INCLUDED_ITREE_INTERP_STATE
