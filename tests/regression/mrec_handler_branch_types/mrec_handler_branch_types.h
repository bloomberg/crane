#ifndef INCLUDED_MREC_HANDLER_BRANCH_TYPES
#define INCLUDED_MREC_HANDLER_BRANCH_TYPES

#include "crane_fn.h"
#include "fn.h"
#include "lazy.h"
#include "obj.h"
#include <atomic>
#include <concepts>
#include <memory>
#include <optional>
#include <stdexcept>
#include <utility>
#include <variant>

struct Nat;
template <typename A, typename B> struct Sum;
template <typename E1, typename E2, typename X> struct Sum1;
template <typename E, typename R, typename itree> struct ItreeF;
template <typename E, typename R> struct Itree;
template <typename T1> struct Functor_itree;
template <typename I>
concept Functor = requires {
  typename I::template F<crane::obj>;
  {
    I::template fmap<crane::obj, crane::obj>(
        std::declval<crane::fn<crane::obj(crane::obj)>>(),
        std::declval<typename I::template F<crane::obj>>())
  } -> std::convertible_to<typename I::template F<crane::obj>>;
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

  Nat add(Nat m) const {
    std::optional<Nat> _root{};
    std::shared_ptr<Nat> *_write = nullptr;
    const Nat *_loop_self = this;
    Nat _loop_m = std::move(m);
    while (true) {
      auto &&_sv = *_loop_self;
      if (std::holds_alternative<typename Nat::O>(_sv.v())) {
        auto _value = std::move(_loop_m);
        (_write ? *(*_write = std::make_shared<Nat>(std::move(_value)))
                : _root.emplace(std::move(_value)));
        break;
      } else {
        const auto &[a0] = std::get<typename Nat::S>(_sv.v());
        auto _cell = typename Nat::S(nullptr);
        Nat &_node =
            (_write ? *(*_write = std::make_shared<Nat>(std::move(_cell)))
                    : _root.emplace(std::move(_cell)));
        _write = &std::get<typename Nat::S>(_node.v_mut()).a0;
        _loop_self = crane_raw(a0);
        continue;
      }
    }
    return std::move(*_root);
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

struct Functor0 {
  template <Functor _tcI0, typename T2, typename T3, typename F0>
  static typename _tcI0::template F<T3> fmap(F0 &&x,
                                             typename _tcI0::template F<T2> x0);
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
      return Itree<T1, T3>::lazy_([=, k = std::move(
                                          k)]() -> typename Itree<T1, T3>::Go {
        return {ItreeF<T1, T3, Itree<T1, T3>>::tauf(subst<T1, T2, T3>(k, t0))};
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
            return Itree<T1, T2>::lazy_([=]() -> typename Itree<T1, T2>::Go {
              return {ItreeF<T1, T2, Itree<T1, T2>>::tauf(
                  iter<T1, T2, T3>(step, a0))};
            });
          } else {
            const auto &[a0] = std::get<typename Sum<T3, T2>::Inr>(lr.v());
            return Itree<T1, T2>::go(ItreeF<T1, T2, Itree<T1, T2>>::retf(a0));
          }
        });
  }

  template <typename T1, typename T2, typename T3>
  static Itree<T1, T3> map(const std::type_identity_t<crane::fn<T3(T2)>> &f,
                           const Itree<T1, T2> &t) {
    return bind<T1, T2, T3>(t, [=](const T2 &x) {
      return Itree<T1, T3>::go(ItreeF<T1, T3, Itree<T1, T3>>::retf(f(x)));
    });
  }
};

template <typename T1> struct Functor_itree {
  template <typename CraneA0> using F = Itree<T1, CraneA0>;

  template <typename CraneA0, typename CraneA1>
  static Itree<T1, CraneA1> fmap(crane::fn<CraneA1(CraneA0)> a0,
                                 Itree<T1, CraneA0> a1) {
    return ITree::template map<T1, CraneA0, CraneA1>(std::move(a0), a1);
  }
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

struct MrecHandlerBranchTypes {
  struct callE {
    // DATA
    Nat a0;

    // ACCESSORS
    callE clone() const { return {a0}; }

    // CREATORS
    static callE call(Nat a0) { return {std::move(a0)}; }
  };

  template <typename P> struct extE {
    // DATA
    P a0;

    // ACCESSORS
    extE<P> clone() const { return {a0}; }

    template <typename CraneU> operator extE<CraneU>() const {
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
    static extE<P> ext(P a0) { return {std::move(a0)}; }
  };
  enum class FailE { FAIL };
  template <typename p, typename x> using OtherE = Sum1<extE<p>, FailE, x>;

  template <typename T1>
  static Itree<Sum1<callE, OtherE<T1, crane::obj>, crane::obj>, Nat>
  ext_call(const Nat &n) {
    return Itree<Sum1<callE, OtherE<T1, crane::obj>, crane::obj>, Nat>::go(
        ItreeF<Sum1<callE, OtherE<T1, crane::obj>, crane::obj>, Nat,
               Itree<Sum1<callE, OtherE<T1, crane::obj>, crane::obj>,
                     Nat>>::retf(n.add(Nat::s(Nat::o()))));
  }

  template <typename T1>
  static Itree<OtherE<T1, crane::obj>, Sum<Nat, Nat>> den(const Nat &n) {
    return Recursion::template mrec<callE, OtherE<T1, crane::obj>,
                                    Sum<Nat, Nat>>(
        [](const callE &call)
            -> Itree<Sum1<callE, Sum1<extE<T1>, FailE, crane::obj>, crane::obj>,
                     crane::obj> {
          const auto &[a0] = call;
          if (std::holds_alternative<typename Nat::O>(a0.v())) {
            return Itree<
                Sum1<callE, OtherE<T1, crane::obj>, crane::obj>,
                crane::obj>::go(ItreeF<crane::obj, Sum<Nat, crane::obj>,
                                       Itree<crane::obj, crane::obj>>::
                                    retf(Sum<crane::obj, crane::obj>::inl(
                                        Nat::o())));
          } else {
            return Functor_itree<
                Sum1<callE, OtherE<T1, crane::obj>, crane::obj>>::
                template fmap<Nat, Sum<Nat, Nat>>(
                    [](const Nat &x) { return Sum<Nat, Nat>::inr(x); },
                    ext_call<T1>(a0));
          }
        },
        callE::call(n));
  }

  static std::optional<Sum<Nat, Nat>>
  run(const Nat &fuel,
      const Itree<Sum1<extE<Nat>, FailE, crane::obj>, Sum<Nat, Nat>> &t);
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
                 den<Nat>(Nat::s(Nat::s(Nat::o()))));
    }();
    if (_cs.has_value()) {
      const Sum<Nat, Nat> &s = *_cs;
      if (std::holds_alternative<typename Sum<Nat, Nat>::Inl>(s.v())) {
        return false;
      } else {
        const auto &[a0] = std::get<typename Sum<Nat, Nat>::Inr>(s.v());
        return a0.eqb(Nat::s(Nat::s(Nat::s(Nat::o()))));
      }
    } else {
      return false;
    }
  }();
};

template <Functor _tcI0, typename T2, typename T3, typename F0>
typename _tcI0::template F<T3>
Functor0::fmap(F0 &&x, typename _tcI0::template F<T2> x0) {
  return _tcI0::template fmap<T2, T3>(x, std::move(x0));
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
    return Itree<T2, T3>::lazy_([=]() -> typename Itree<T2, T3>::Go {
      return {ItreeF<T2, T3, Itree<T2, T3>>::tauf(
          Recursion::template interp_mrec<T1, T2, T3>(ctx, t0))};
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
            [=]() ->
            typename Itree<T2,
                           Sum<Itree<Sum1<T1, T2, crane::obj>, T3>, T3>>::Go {
              return {
                  ItreeF<
                      T2, Sum<Itree<Sum1<T1, T2, crane::obj>, T3>, T3>,
                      Itree<T2, Sum<Itree<Sum1<T1, T2, crane::obj>, T3>, T3>>>::
                      retf(Sum<Itree<Sum1<T1, T2, crane::obj>, T3>, T3>::inl(
                          ITree::template bind<Sum1<T1, T2, crane::obj>,
                                               crane::obj, T3>(
                              crane_call_erased(ctx, a00), e)))};
            });
      } else {
        const auto &[a00] =
            std::get<typename Sum1<T1, T2, crane::obj>::Inr1>(x.v());
        return Itree<T2, Sum<Itree<Sum1<T1, T2, crane::obj>, T3>, T3>>::go(
            ItreeF<T2, Sum<Itree<Sum1<T1, T2, crane::obj>, T3>, T3>,
                   Itree<T2, Sum<Itree<Sum1<T1, T2, crane::obj>, T3>, T3>>>::
                visf(
                    a00,
                    crane::fn<
                        Itree<T2, Sum<Itree<Sum1<T1, T2, crane::obj>, T3>, T3>>(
                            crane::obj)>([=](const crane::obj &x0)
                                             -> Itree<
                                                 T2, Sum<Itree<Sum1<T1, T2,
                                                                    crane::obj>,
                                                               T3>,
                                                         T3>> {
                      return Itree<
                          T2, Sum<Itree<Sum1<T1, T2, crane::obj>, T3>, T3>>::
                          lazy_([=]()
                                    -> typename Itree<
                                        T2,
                                        Sum<Itree<Sum1<T1, T2, crane::obj>, T3>,
                                            T3>>::Go {
                            return {ItreeF<
                                T2,
                                Sum<Itree<Sum1<T1, T2, crane::obj>, T3>, T3>,
                                Itree<T2,
                                      Sum<Itree<Sum1<T1, T2, crane::obj>, T3>,
                                          T3>>>::
                                        retf(Sum<
                                             Itree<Sum1<T1, T2, crane::obj>,
                                                   T3>,
                                             T3>::inl(crane_call_erased(e,
                                                                        x0)))};
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
            return Itree<T2, T3>::lazy_([=]() -> typename Itree<T2, T3>::Go {
              return {ItreeF<T2, T3, Itree<T2, T3>>::tauf(
                  Recursion::template interp_mrec<T1, T2, T3>(ctx, a0))};
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

#endif // INCLUDED_MREC_HANDLER_BRANCH_TYPES
