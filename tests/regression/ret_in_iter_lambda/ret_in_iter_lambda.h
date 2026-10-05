#ifndef INCLUDED_RET_IN_ITER_LAMBDA
#define INCLUDED_RET_IN_ITER_LAMBDA

#include "crane_fn.h"
#include "fn.h"
#include "lazy.h"
#include "obj.h"
#include <atomic>
#include <concepts>
#include <memory>
#include <stdexcept>
#include <utility>
#include <variant>

struct Nat;
template <typename A, typename B> struct Sum;
template <typename E1, typename E2, typename X> struct Sum1;
template <typename E, typename R, typename itree> struct ItreeF;
template <typename E, typename R> struct Itree;
template <typename T1> struct Monad_itree;
template <typename I>
concept Monad = requires {
  typename I::template m<crane::obj>;
  {
    I::template ret<crane::obj>(std::declval<crane::obj>())
  } -> std::convertible_to<typename I::template m<crane::obj>>;
  {
    I::bind(std::declval<typename I::template m<crane::obj>>(),
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
  Nat(Nat &&) = default;
  Nat &operator=(Nat &&) = default;

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

struct Monad0 {
  template <Monad _tcI0, typename T2>
  static typename _tcI0::template m<T2> ret(const T2 &x);
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
};

template <typename T1> struct Monad_itree {
  template <typename CraneA0> using m = Itree<T1, CraneA0>;

  template <typename CraneA0> static Itree<T1, CraneA0> ret(CraneA0 x) {
    return Itree<T1, CraneA0>::go(
        ItreeF<crane::obj, crane::obj, Itree<crane::obj, crane::obj>>::retf(
            std::move(x)));
  }

  static Itree<T1, crane::obj>
  bind(Itree<T1, crane::obj> a0,
       crane::fn<Itree<T1, crane::obj>(crane::obj)> a1) {
    return ITree::template bind<T1, crane::obj, crane::obj>(a0, std::move(a1));
  }
};

struct RetInIterLambda {
  template <typename P> struct aE {
    // DATA
    P a0;

    // ACCESSORS
    aE<P> clone() const { return {a0}; }

    template <typename CraneU> operator aE<CraneU>() const {
      return {[&]() -> CraneU {
        if constexpr (crane_convertible<CraneU, const P &>) {
          return crane_convert<CraneU>(a0);
        } else {
          throw std::logic_error(
              "unreachable: inactive constructor field at this instantiation");
        }
      }()};
    }

    // CREATORS
    static aE<P> a(P a0) { return {std::move(a0)}; }
  };
  enum class BE { B };
  template <typename p, typename x> using AllE = Sum1<aE<p>, BE, x>;
  template <typename p, typename r> using top = Itree<AllE<p, crane::obj>, r>;

  template <typename T1> static top<T1, Nat> count(const Nat &n) {
    return ITree::template iter<AllE<T1, crane::obj>, Nat, Nat>(
        [=](const Nat &k) -> Itree<AllE<T1, crane::obj>, Sum<Nat, Nat>> {
          if (k.eqb(n)) {
            return Monad0::template ret<Monad_itree<AllE<T1, crane::obj>>,
                                        Sum<Nat, Nat>>(Sum<Nat, Nat>::inr(k));
          } else {
            return Monad0::template ret<Monad_itree<AllE<T1, crane::obj>>,
                                        Sum<Nat, Nat>>(
                Sum<Nat, Nat>::inl(Nat::s(k)));
          }
        },
        Nat::o());
  }

  static inline const Itree<AllE<Nat, crane::obj>, Nat> c =
      count<Nat>(Nat::s(Nat::s(Nat::s(Nat::o()))));
};

template <Monad _tcI0, typename T2>
typename _tcI0::template m<T2> Monad0::ret(const T2 &x) {
  return _tcI0::template ret<T2>(x);
}

#endif // INCLUDED_RET_IN_ITER_LAMBDA
