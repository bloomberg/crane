#ifndef INCLUDED_MREC_FACT
#define INCLUDED_MREC_FACT

#include "crane_fn.h"
#include "fn.h"
#include "lazy.h"
#include "obj.h"
#include "shared_block.h"
#include <atomic>
#include <cstdint>
#include <stdexcept>
#include <utility>
#include <variant>

template <typename A, typename B> struct Sum;
template <typename E1, typename E2, typename X> struct Sum1;
template <typename E, typename R, typename itree> struct ItreeF;
template <typename E, typename R> struct Itree;

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

  template <typename CraneU0, typename CraneU1, typename CraneU2>
  Sum1(const Sum1<CraneU0, CraneU1, CraneU2> &_other)
      : v_([&]() -> variant_t {
          if (std::holds_alternative<
                  typename Sum1<CraneU0, CraneU1, CraneU2>::Inl1>(_other.v())) {
            const auto &[a0] =
                std::get<typename Sum1<CraneU0, CraneU1, CraneU2>::Inl1>(
                    _other.v());
            return Inl1{[&]() -> E1 {
              if constexpr (crane_convertible<E1, const CraneU0 &>) {
                return crane_convert<E1>(a0);
              } else {
                throw std::logic_error("unreachable: inactive constructor "
                                       "field at this instantiation");
              }
            }()};
          } else {
            const auto &[a0] =
                std::get<typename Sum1<CraneU0, CraneU1, CraneU2>::Inr1>(
                    _other.v());
            return Inr1{[&]() -> E2 {
              if constexpr (crane_convertible<E2, const CraneU1 &>) {
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
                  typename ItreeF<CraneU0, CraneU1, CraneU2>::RetF>(
                  _other.v())) {
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
                      throw std::logic_error(
                          "unreachable: inactive constructor field at this "
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
  subst(std::type_identity_t<crane::fn<Itree<T1, T3>(T2)>> k,
        const Itree<T1, T2> &u) {
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
      return Itree<T1, T3>::lazy_([=, k = std::move(k)]() -> Itree<T1, T3> {
        return Itree<T1, T3>::go(
            ItreeF<T1, T3, Itree<T1, T3>>::tauf(subst<T1, T2, T3>(k, t0)));
      });
    } else {
      const auto &[x, e0] =
          std::get<typename ItreeF<T1, T2, Itree<T1, T2>>::VisF>(_sv.v());
      return Itree<T1, T3>::go(ItreeF<T1, T3, Itree<T1, T3>>::visf(
          x, crane::fn<Itree<T1, T3>(crane::obj)>(
                 [=, k = std::move(k)](const crane::obj &x0) -> Itree<T1, T3> {
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
  static Itree<T1, T2>
  iter(const std::type_identity_t<crane::fn<Itree<T1, Sum<T3, T2>>(T3)>> &step,
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

struct Subevent {
  template <typename T1, typename T2, typename T3>
  static crane::rebind_t<T2, T3>
  subevent(ReSum<crane::obj, IFun<crane::obj, crane::obj>> h,
           crane::rebind_t<T1, T3> x);
};

struct Recursion {
  template <typename T1, typename T2, typename T3>
  static Itree<T2, T3> interp_mrec(
      const std::type_identity_t<
          crane::fn<Itree<Sum1<T1, T2, crane::obj>, crane::obj>(T1)>> &ctx,
      const Itree<Sum1<T1, T2, crane::obj>, T3> &i);
  template <typename T1, typename T2, typename T3>
  static Itree<T2, T3>
  mrec(const std::type_identity_t<
           crane::fn<Itree<Sum1<T1, T2, crane::obj>, crane::obj>(T1)>> &ctx,
       crane::rebind_t<T1, T3> d);
};

/// Factorial through coq-itree's mrec: each recursive call is an event
/// interp_mrec answers by running the body again.  interp_mrec passes
/// iter its step as a lambda, so it is the specialized interpreter that
/// runs here.
struct MrecFact {
  struct call {
    // DATA
    uint64_t n;

    // ACCESSORS
    call clone() const { return {n}; }

    // CREATORS
    static call fact(uint64_t n) { return {n}; }
  };

  template <typename T1>
  static Itree<Sum1<call, crane::obj, crane::obj>, T1> body(const call &c) {
    static const auto resum_id = crane::immortal(
        CategoryOps::template ReSum_id<crane::obj,
                                       crane::fn<crane::obj(crane::obj)>>(
            [](crane::obj) {
              return crane_erase_global<Function::Id_IFun, crane::obj>();
            },
            crane::obj()));
    const auto &[n0] = c;
    if (n0 <= 0) {
      return Itree<Sum1<call, crane::obj, crane::obj>, T1>::go(
          ItreeF<crane::obj, T1, Itree<crane::obj, T1>>::retf(UINT64_C(1)));
    } else {
      uint64_t m = n0 - 1;
      return ITree::template bind<Sum1<call, crane::obj, crane::obj>, uint64_t,
                                  uint64_t>(
          ITree::template trigger<Sum1<call, crane::obj, crane::obj>, uint64_t>(
              Subevent::template subevent<
                  crane::obj, Sum1<call, crane::obj, crane::obj>, uint64_t>(
                  resum_id, Sum1<crane::obj, crane::obj, crane::obj>::inl1(
                                call::fact(m)))),
          [=](uint64_t r) {
            return Itree<Sum1<call, crane::obj, crane::obj>, T1>::lazy_(
                [=]() -> Itree<Sum1<call, crane::obj, crane::obj>, T1> {
                  return Itree<Sum1<call, crane::obj, crane::obj>, T1>::go(
                      ItreeF<crane::obj, T1, Itree<crane::obj, T1>>::retf(
                          (n0 * r)));
                });
          });
    }
  }

  static Itree<crane::obj, uint64_t> fact(uint64_t n);
};

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
Subevent::subevent(ReSum<crane::obj, IFun<crane::obj, crane::obj>> h,
                   crane::rebind_t<T1, T3> x) {
  return crane_any_cast<crane::rebind_t<T2, T3>>(
      CategoryOps::resum(crane::obj(), crane::obj(), h)(std::move(x)));
}

template <typename T1, typename T2, typename T3>
Itree<T2, T3> Recursion::interp_mrec(
    const std::type_identity_t<
        crane::fn<Itree<Sum1<T1, T2, crane::obj>, crane::obj>(T1)>> &ctx,
    const Itree<Sum1<T1, T2, crane::obj>, T3> &i) {
  auto &&_sv = i.observe();
  if (std::holds_alternative<
          typename ItreeF<Sum1<T1, T2, crane::obj>, T3,
                          Itree<Sum1<T1, T2, crane::obj>, T3>>::RetF>(
          _sv.v())) {
    const auto &[r0] =
        std::get<typename ItreeF<Sum1<T1, T2, crane::obj>, T3,
                                 Itree<Sum1<T1, T2, crane::obj>, T3>>::RetF>(
            _sv.v());
    return Itree<T2, T3>::go(ItreeF<T2, T3, Itree<T2, T3>>::retf(r0));
  } else if (std::holds_alternative<
                 typename ItreeF<Sum1<T1, T2, crane::obj>, T3,
                                 Itree<Sum1<T1, T2, crane::obj>, T3>>::TauF>(
                 _sv.v())) {
    const auto &[t0] =
        std::get<typename ItreeF<Sum1<T1, T2, crane::obj>, T3,
                                 Itree<Sum1<T1, T2, crane::obj>, T3>>::TauF>(
            _sv.v());
    return Itree<T2, T3>::lazy_([=]() -> Itree<T2, T3> {
      return Itree<T2, T3>::go(ItreeF<T2, T3, Itree<T2, T3>>::tauf(
          Recursion::template interp_mrec<T1, T2, T3>(ctx, t0)));
    });
  } else {
    const auto &[x, e] =
        std::get<typename ItreeF<Sum1<T1, T2, crane::obj>, T3,
                                 Itree<Sum1<T1, T2, crane::obj>, T3>>::VisF>(
            _sv.v());
    auto step = [&]() {
      if (std::holds_alternative<typename Sum1<T1, T2, crane::obj>::Inl1>(
              x.v())) {
        const auto &[a00] =
            std::get<typename Sum1<T1, T2, crane::obj>::Inl1>(x.v());
        return Itree<T2, Sum<Itree<Sum1<T1, T2, crane::obj>, T3>, T3>>::lazy_(
            [=]() -> Itree<T2, Sum<Itree<Sum1<T1, T2, crane::obj>, T3>, T3>> {
              return Itree<T2, Sum<Itree<Sum1<T1, T2, crane::obj>, T3>, T3>>::
                  go(ItreeF<
                      crane::obj, Sum<Itree<Sum1<T1, T2, crane::obj>, T3>, T3>,
                      Itree<crane::obj,
                            Sum<Itree<Sum1<T1, T2, crane::obj>, T3>, T3>>>::
                         retf(Sum<Itree<Sum1<T1, T2, crane::obj>, T3>, T3>::inl(
                             ITree::template bind<Sum1<T1, T2, crane::obj>,
                                                  crane::obj, T3>(
                                 crane_call_erased(ctx, a00), e))));
            });
      } else {
        const auto &[a00] =
            std::get<typename Sum1<T1, T2, crane::obj>::Inr1>(x.v());
        return Itree<T2, Sum<Itree<Sum1<T1, T2, crane::obj>, T3>, T3>>::go(
            ItreeF<crane::obj, Sum<Itree<Sum1<T1, T2, crane::obj>, T3>, T3>,
                   Itree<crane::obj,
                         Sum<Itree<Sum1<T1, T2, crane::obj>, T3>, T3>>>::
                visf(
                    a00,
                    crane::fn<
                        Itree<crane::obj,
                              Sum<Itree<Sum1<T1, T2, crane::obj>, T3>, T3>>(
                            crane::obj)>(
                        [=](const crane::obj &x0)
                            -> Itree<
                                crane::obj,
                                Sum<Itree<Sum1<T1, T2, crane::obj>, T3>, T3>> {
                          return Itree<
                              crane::obj,
                              Sum<Itree<Sum1<T1, T2, crane::obj>, T3>,
                                  T3>>::lazy_([=]()
                                                  -> Itree<
                                                      crane::obj,
                                                      Sum<Itree<
                                                              Sum1<T1, T2,
                                                                   crane::obj>,
                                                              T3>,
                                                          T3>> {
                            return Itree<
                                crane::obj,
                                Sum<Itree<Sum1<T1, T2, crane::obj>, T3>, T3>>::
                                go(ItreeF<
                                    crane::obj,
                                    Sum<Itree<Sum1<T1, T2, crane::obj>, T3>,
                                        T3>,
                                    Itree<
                                        crane::obj,
                                        Sum<Itree<Sum1<T1, T2, crane::obj>, T3>,
                                            T3>>>::
                                       retf(Sum<
                                            Itree<Sum1<T1, T2, crane::obj>, T3>,
                                            T3>::inl(crane_call_erased(e,
                                                                       x0))));
                          });
                        })));
      }
    }();
    return ITree::template bind<
        T2, Sum<Itree<Sum1<T1, T2, crane::obj>, T3>, T3>, T3>(
        std::move(step), [=](const auto &lr) -> Itree<T2, T3> {
          if (std::holds_alternative<
                  typename Sum<Itree<Sum1<T1, T2, crane::obj>, T3>, T3>::Inl>(
                  lr.v())) {
            const auto &[a0] = std::get<
                typename Sum<Itree<Sum1<T1, T2, crane::obj>, T3>, T3>::Inl>(
                lr.v());
            return Itree<T2, T3>::lazy_([=]() -> Itree<T2, T3> {
              return Itree<T2, T3>::go(ItreeF<T2, T3, Itree<T2, T3>>::tauf(
                  Recursion::template interp_mrec<T1, T2, T3>(ctx, a0)));
            });
          } else {
            const auto &[a0] = std::get<
                typename Sum<Itree<Sum1<T1, T2, crane::obj>, T3>, T3>::Inr>(
                lr.v());
            return Itree<T2, T3>::go(ItreeF<T2, T3, Itree<T2, T3>>::retf(a0));
          }
        });
  }
}

template <typename T1, typename T2, typename T3>
Itree<T2, T3> Recursion::mrec(
    const std::type_identity_t<
        crane::fn<Itree<Sum1<T1, T2, crane::obj>, crane::obj>(T1)>> &ctx,
    crane::rebind_t<T1, T3> d) {
  return Recursion::template interp_mrec<T1, T2, T3>(ctx, ctx(std::move(d)));
}

#endif // INCLUDED_MREC_FACT
