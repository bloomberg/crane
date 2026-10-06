#ifndef INCLUDED_INTERP_STATE_CASE_HANDLER
#define INCLUDED_INTERP_STATE_CASE_HANDLER

#include "crane_fn.h"
#include "fn.h"
#include "lazy.h"
#include "obj.h"
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
template <typename E1, typename E2, typename X> struct Sum1;
template <typename E, typename R, typename itree> struct ItreeF;
template <typename E, typename R> struct Itree;
template <typename T1> struct Functor_itree;
template <typename T1> struct Monad_itree;
template <typename T1> struct MonadIter_itree;
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

struct Monad0 {
  template <Monad _tcI0, typename T2>
  static typename _tcI0::template m<T2> ret(const T2 &x);
  template <Monad _tcI0, typename T2, typename T3, typename F1>
  static typename _tcI0::template m<T3> bind(typename _tcI0::template m<T2> x,
                                             F1 &&x0);
};

template <typename obj, typename c> using Id_ = crane::fn<c(obj)>;
template <typename obj, typename c>
using Cat = crane::fn<c(obj, obj, obj, c, c)>;
template <typename obj, typename c>
using Case = crane::fn<c(obj, obj, obj, c, c)>;
template <typename obj, typename c> using Inl = crane::fn<c(obj, obj)>;
template <typename obj, typename c> using Inr = crane::fn<c(obj, obj)>;
template <typename obj, typename c> using ReSum = c;

struct CategoryOps {
  template <typename T1, typename T2>
  static T2 id_(std::type_identity_t<Id_<T1, T2>> id_0, T1 x0_);
  template <typename T1, typename T2>
  static T2 cat(std::type_identity_t<Cat<T1, T2>> cat0, const T1 &x0_,
                const T1 &x1_, const T1 &x2_, const T2 &x3_, T2 x4_);
  template <typename T1, typename T2, typename F0>
  static T2 case_(F0 &&_x, std::type_identity_t<Case<T1, T2>> case0,
                  const T1 &x0_, const T1 &x1_, const T1 &x2_, const T2 &x3_,
                  T2 x4_);
  template <typename T1, typename T2, typename F0>
  static T2 inl_(F0 &&_x, std::type_identity_t<Inl<T1, T2>> inl0, const T1 &x0_,
                 T1 x1_);
  template <typename T1, typename T2, typename F0>
  static T2 inr_(F0 &&_x, std::type_identity_t<Inr<T1, T2>> inr0, const T1 &x0_,
                 T1 x1_);
  template <typename T1, typename T2>
  static T2 resum(const T1 &_x, const T1 &_x0, T2 reSum);
  template <typename T1, typename T2>
  static ReSum<T1, T2> ReSum_id(std::type_identity_t<Id_<T1, T2>> x0_,
                                const T1 &x1_);
  template <typename T1, typename T2, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, const T1 &, const T1 &>
  static ReSum<T1, T2> ReSum_inl(F0 &&bif, std::type_identity_t<Cat<T1, T2>> h0,
                                 std::type_identity_t<Inl<T1, T2>> h2,
                                 const T1 &a, const T1 &b, const T1 &c, T2 h4);
  template <typename T1, typename T2, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, const T1 &, const T1 &>
  static ReSum<T1, T2> ReSum_inr(F0 &&bif, std::type_identity_t<Cat<T1, T2>> h0,
                                 std::type_identity_t<Inr<T1, T2>> h3,
                                 const T1 &a, const T1 &b, const T1 &c, T2 h4);
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

struct Monads {
  template <typename s, template <typename> class m, typename a>
  using stateT = crane::fn<m<std::pair<s, a>>(s)>;

  template <Functor _tcI0, typename T1> struct Functor_stateT {
    template <typename CraneA0>
    using F = crane::fn<typename _tcI0::template F<std::pair<T1, CraneA0>>(T1)>;

    template <typename CraneA0, typename CraneA1>
    static crane::fn<typename _tcI0::template F<std::pair<T1, CraneA1>>(T1)>
    fmap(crane::fn<CraneA1(CraneA0)> f,
         crane::fn<typename _tcI0::template F<std::pair<T1, CraneA0>>(T1)>
             run0) {
      return [=, f = std::move(f), run0 = std::move(run0)](const T1 &s) {
        return Functor0::template fmap<_tcI0, std::pair<T1, CraneA0>,
                                       std::pair<T1, CraneA1>>(
            [=](const std::pair<T1, CraneA0> &sa) {
              return std::make_pair(sa.first, f(sa.second));
            },
            run0(s));
      };
    }
  };

  template <Monad _tcI0, typename T1> struct Monad_stateT {
    template <typename CraneA0>
    using m = crane::fn<typename _tcI0::template m<std::pair<T1, CraneA0>>(T1)>;

    template <typename CraneA0>
    static crane::fn<typename _tcI0::template m<std::pair<T1, CraneA0>>(T1)>
    ret(CraneA0 a) {
      return [=, a = std::move(a)](const T1 &s) {
        return Monad0::template ret<_tcI0, std::pair<T1, CraneA0>>(
            std::make_pair(s, a));
      };
    }

    template <typename CraneA0, typename CraneA1>
    static crane::fn<typename _tcI0::template m<std::pair<T1, CraneA1>>(T1)>
    bind(crane::fn<typename _tcI0::template m<std::pair<T1, CraneA0>>(T1)> t,
         crane::fn<crane::fn<
             typename _tcI0::template m<std::pair<T1, CraneA1>>(T1)>(CraneA0)>
             k) {
      return [=, k = std::move(k), t = std::move(t)](const T1 &s) {
        return Monad0::template bind<_tcI0, std::pair<T1, CraneA0>,
                                     std::pair<T1, CraneA1>>(
            t(s), [=](const std::pair<T1, CraneA0> &sa) {
              return crane::apply2(k, sa.second, sa.first);
            });
      };
    }
  };
};

template <typename I>
concept MonadIter = requires {
  typename I::template M<crane::obj>;
  {
    I::template iter<crane::obj, crane::obj>(
        std::declval<crane::fn<
            typename I::template M<Sum<crane::obj, crane::obj>>(crane::obj)>>(),
        std::declval<crane::obj>())
  } -> std::convertible_to<typename I::template M<crane::obj>>;
};

template <MonadIter _tcI0, typename T2, typename T3, typename F0>
typename _tcI0::template M<T2> iter(F0 &&x, const T3 &x0) {
  return _tcI0::template iter<T2, T3>(x, x0);
}

template <Monad _tcI0, MonadIter _tcI1, typename T1> struct MonadIter_stateT0 {
  template <typename CraneA0> using m = typename _tcI0::template m<CraneA0>;
  template <typename CraneA0>
  using M = typename Monads::template stateT<T1, _tcI1::template M, CraneA0>;

  template <typename CraneA0, typename CraneA1>
  static typename Monads::template stateT<T1, _tcI1::template M, CraneA0>
  iter(crane::fn<typename Monads::template stateT<
           T1, _tcI1::template M, Sum<CraneA1, CraneA0>>(CraneA1)>
           step,
       CraneA1 i) {
    return [=, i = std::move(i), step = std::move(step)](const T1 &s) {
      return _tcI1::template iter<std::pair<T1, CraneA0>,
                                  std::pair<T1, CraneA1>>(
          [=](const std::pair<T1, CraneA1> &si) {
            T1 s0 = si.first;
            CraneA1 i0 = si.second;
            return Monad0::template bind<
                _tcI0, std::pair<T1, Sum<CraneA1, CraneA0>>,
                Sum<std::pair<T1, CraneA1>, std::pair<T1, CraneA0>>>(
                crane::apply2(step, i0, s0),
                [](const std::pair<T1, Sum<CraneA1, CraneA0>> &si_) {
                  return Monad0::template ret<
                      _tcI0, Sum<std::pair<T1, CraneA1>,
                                 std::pair<T1, CraneA0>>>([&]() {
                    auto &&_sv = si_.second;
                    if (std::holds_alternative<
                            typename Sum<CraneA1, CraneA0>::Inl>(_sv.v())) {
                      const auto &[a0] =
                          std::get<typename Sum<CraneA1, CraneA0>::Inl>(
                              _sv.v());
                      return Sum<
                          std::pair<T1, CraneA1>,
                          std::pair<T1, CraneA0>>::inl(std::make_pair(si_.first,
                                                                      a0));
                    } else {
                      const auto &[a0] =
                          std::get<typename Sum<CraneA1, CraneA0>::Inr>(
                              _sv.v());
                      return Sum<
                          std::pair<T1, CraneA1>,
                          std::pair<T1, CraneA0>>::inr(std::make_pair(si_.first,
                                                                      a0));
                    }
                  }());
                });
          },
          std::make_pair(s, i));
    };
  }
};

template <typename e, typename f> using IFun = crane::fn<f(e)>;

struct Function {
  static crane::obj Id_IFun(crane::obj e);
  static crane::obj Cat_IFun(IFun<crane::obj, crane::obj> f1,
                             IFun<crane::obj, crane::obj> f2, crane::obj e);
  template <typename T1, typename T2, typename T4, typename F0, typename F1>
  static std::invoke_result_t<F0 &, crane::rebind_t<T1, T4> &>
  case_sum1(F0 &&f, F1 &&g, const Sum1<T1, T2, T4> &ab);
  static crane::obj Case_sum1(IFun<crane::obj, crane::obj> x,
                              IFun<crane::obj, crane::obj> x0, crane::obj x1);
  static crane::obj Inl_sum1(crane::obj x);
  static crane::obj Inr_sum1(crane::obj x);
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

  template <typename T1, typename T2, typename T3>
  static Itree<T1, T3> map(const std::type_identity_t<crane::fn<T3(T2)>> &f,
                           const Itree<T1, T2> &t) {
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
  template <typename CraneA0> using F = Itree<T1, CraneA0>;

  template <typename CraneA0, typename CraneA1>
  static Itree<T1, CraneA1> fmap(crane::fn<CraneA1(CraneA0)> a0,
                                 Itree<T1, CraneA0> a1) {
    return ITree::template map<T1, CraneA0, CraneA1>(std::move(a0), a1);
  }
};

template <typename T1> struct Monad_itree {
  template <typename CraneA0> using m = Itree<T1, CraneA0>;

  template <typename CraneA0> static Itree<T1, CraneA0> ret(CraneA0 x) {
    return Itree<T1, CraneA0>::go(
        ItreeF<crane::obj, crane::obj, Itree<crane::obj, crane::obj>>::retf(
            std::move(x)));
  }

  template <typename CraneA0, typename CraneA1>
  static Itree<T1, CraneA1> bind(Itree<T1, CraneA0> a0,
                                 crane::fn<Itree<T1, CraneA1>(CraneA0)> a1) {
    return ITree::template bind<T1, CraneA0, CraneA1>(a0, std::move(a1));
  }
};

template <typename T1> struct MonadIter_itree {
  template <typename CraneA0> using M = Itree<T1, CraneA0>;

  template <typename CraneA0, typename CraneA1>
  static Itree<T1, CraneA0>
  iter(crane::fn<Itree<T1, Sum<CraneA1, CraneA0>>(CraneA1)> a0, CraneA1 a1) {
    return ITree::template iter<T1, CraneA0, CraneA1>(std::move(a0),
                                                      std::move(a1));
  }
};

struct Subevent {
  template <typename T1, typename T2, typename T3>
  static crane::rebind_t<T2, T3>
  subevent(ReSum<crane::obj, IFun<crane::obj, crane::obj>> h0,
           crane::rebind_t<T1, T3> x);
};

struct Interp {
  template <MonadIter _tcI0, Monad _tcI1, Functor _tcI2, typename T1,
            typename T3>
  static typename _tcI0::template M<T3>
  interp(std::type_identity_t<
             crane::fn<typename _tcI0::template M<crane::obj>(T1)>>
             h0,
         Itree<T1, T3> x0_);
};

struct State {
  template <MonadIter _tcI0, Monad _tcI1, Functor _tcI2, typename T1,
            typename T3, typename T4>
  static Monads::template stateT<T3, _tcI0::template M, T4> interp_state(
      std::type_identity_t<crane::fn<
          Monads::template stateT<T3, _tcI0::template M, crane::obj>(T1)>>
          h0,
      Itree<T1, T4> x);
};

struct InterpStateCaseHandler {
  enum class GetE { GET };
  enum class IncE { INC };

  struct noE {
    noE() = delete;
  };

  static inline const Itree<Sum1<GetE, IncE, crane::obj>, Nat> prog = []() {
    return ITree::template bind<Sum1<GetE, IncE, crane::obj>, std::monostate,
                                Nat>(
        ITree::template trigger<Sum1<GetE, IncE, crane::obj>, std::monostate>(
            Subevent::template subevent<IncE, Sum1<GetE, IncE, crane::obj>,
                                        std::monostate>(
                CategoryOps::template ReSum_inr<
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
                      return crane_erase_fn<crane::obj>(Function::Inr_sum1);
                    },
                    crane::obj(), crane::obj(), crane::obj(),
                    CategoryOps::template ReSum_id<
                        crane::obj, crane::fn<crane::obj(crane::obj)>>(
                        [](crane::obj) {
                          return crane_erase_fn<crane::obj>(Function::Id_IFun);
                        },
                        crane::obj())),
                IncE::INC)),
        [](std::monostate) {
          return ITree::template bind<Sum1<GetE, IncE, crane::obj>, Nat, Nat>(
              ITree::template trigger<Sum1<GetE, IncE, crane::obj>, Nat>(
                  Subevent::template subevent<
                      GetE, Sum1<GetE, IncE, crane::obj>, Nat>(
                      CategoryOps::template ReSum_inl<
                          crane::obj, crane::fn<crane::obj(crane::obj)>>(
                          [](const auto &, const auto &) {
                            return crane::obj();
                          },
                          [](crane::obj, crane::obj, crane::obj, const auto &x,
                             crane::fn<crane::obj(crane::obj)> x0) {
                            return [=](crane::obj _x0) -> crane::obj {
                              return Function::Cat_IFun(
                                  x,
                                  crane::any_cast<IFun<crane::obj, crane::obj>>(
                                      x0),
                                  _x0);
                            };
                          },
                          [](crane::obj, crane::obj) {
                            return crane_erase_fn<crane::obj>(
                                Function::Inl_sum1);
                          },
                          crane::obj(), crane::obj(), crane::obj(),
                          CategoryOps::template ReSum_id<
                              crane::obj, crane::fn<crane::obj(crane::obj)>>(
                              [](crane::obj) {
                                return crane_erase_fn<crane::obj>(
                                    Function::Id_IFun);
                              },
                              crane::obj())),
                      GetE::GET)),
              [](const Nat &x) {
                return ITree::template bind<Sum1<GetE, IncE, crane::obj>,
                                            std::monostate, Nat>(
                    ITree::template trigger<Sum1<GetE, IncE, crane::obj>,
                                            std::monostate>(
                        Subevent::template subevent<
                            IncE, Sum1<GetE, IncE, crane::obj>, std::monostate>(
                            CategoryOps::template ReSum_inr<
                                crane::obj, crane::fn<crane::obj(crane::obj)>>(
                                [](const auto &, const auto &) {
                                  return crane::obj();
                                },
                                [](crane::obj, crane::obj, crane::obj,
                                   const auto &x0,
                                   crane::fn<crane::obj(crane::obj)> x1) {
                                  return [=](crane::obj _x0) -> crane::obj {
                                    return Function::Cat_IFun(
                                        x0,
                                        crane::any_cast<
                                            IFun<crane::obj, crane::obj>>(x1),
                                        _x0);
                                  };
                                },
                                [](crane::obj, crane::obj) {
                                  return crane_erase_fn<crane::obj>(
                                      Function::Inr_sum1);
                                },
                                crane::obj(), crane::obj(), crane::obj(),
                                CategoryOps::template ReSum_id<
                                    crane::obj,
                                    crane::fn<crane::obj(crane::obj)>>(
                                    [](crane::obj) {
                                      return crane_erase_fn<crane::obj>(
                                          Function::Id_IFun);
                                    },
                                    crane::obj())),
                            IncE::INC)),
                    [=](std::monostate) {
                      return ITree::template bind<Sum1<GetE, IncE, crane::obj>,
                                                  Nat, Nat>(
                          ITree::template trigger<Sum1<GetE, IncE, crane::obj>,
                                                  Nat>(
                              Subevent::template subevent<
                                  GetE, Sum1<GetE, IncE, crane::obj>, Nat>(
                                  CategoryOps::template ReSum_inl<
                                      crane::obj,
                                      crane::fn<crane::obj(crane::obj)>>(
                                      [](const auto &, const auto &) {
                                        return crane::obj();
                                      },
                                      [](crane::obj, crane::obj, crane::obj,
                                         const auto &x0,
                                         crane::fn<crane::obj(crane::obj)> x1) {
                                        return [=](crane::obj _x0)
                                                   -> crane::obj {
                                          return Function::Cat_IFun(
                                              x0,
                                              crane::any_cast<
                                                  IFun<crane::obj, crane::obj>>(
                                                  x1),
                                              _x0);
                                        };
                                      },
                                      [](crane::obj, crane::obj) {
                                        return crane_erase_fn<crane::obj>(
                                            Function::Inl_sum1);
                                      },
                                      crane::obj(), crane::obj(), crane::obj(),
                                      CategoryOps::template ReSum_id<
                                          crane::obj,
                                          crane::fn<crane::obj(crane::obj)>>(
                                          [](crane::obj) {
                                            return crane_erase_fn<crane::obj>(
                                                Function::Id_IFun);
                                          },
                                          crane::obj())),
                                  GetE::GET)),
                          [=](Nat y) {
                            return Itree<
                                Sum1<GetE, IncE, crane::obj>,
                                Nat>::lazy_([=]() -> Itree<Sum1<GetE, IncE,
                                                                crane::obj>,
                                                           Nat> {
                              return Itree<Sum1<GetE, IncE, crane::obj>, Nat>::
                                  go(ItreeF<Sum1<GetE, IncE, crane::obj>, Nat,
                                            Itree<Sum1<GetE, IncE, crane::obj>,
                                                  Nat>>::retf(x.add(y)));
                            });
                          });
                    });
              });
        });
  }();
  template <typename CraneTcArg>
  using crane_carrier_tc_73ef07e9f18b86f9 = Itree<noE, CraneTcArg>;

  template <typename T1>
  static Monads::template stateT<Nat, crane_carrier_tc_73ef07e9f18b86f9, T1>
  h_get(GetE) {
    return [](const Nat &s) {
      return Itree<noE, std::pair<Nat, T1>>::go(
          ItreeF<noE, std::pair<Nat, T1>, Itree<noE, std::pair<Nat, T1>>>::retf(
              std::make_pair(s, s)));
    };
  }

  template <typename T1>
  static Monads::template stateT<Nat, crane_carrier_tc_73ef07e9f18b86f9, T1>
  h_inc(IncE) {
    return [](const Nat &s) {
      return Itree<noE, std::pair<Nat, T1>>::go(
          ItreeF<noE, std::pair<Nat, T1>, Itree<noE, std::pair<Nat, T1>>>::retf(
              std::make_pair(Nat::s(s), []() -> T1 {
                if constexpr (crane_convertible<T1, const std::monostate &>) {
                  return crane_convert<T1>(std::monostate{});
                } else {
                  throw std::logic_error(
                      "unreachable: impossible dependent match branch");
                }
              }())));
    };
  }

  template <typename T1>
  static Monads::template stateT<Nat, crane_carrier_tc_73ef07e9f18b86f9, T1>
  h(Sum1<GetE, IncE, T1> x) {
    return [=, x = std::move(x)](Nat x0) {
      return crane_convert<Itree<noE, std::pair<Nat, T1>>>(
          crane::any_cast<
              crane::fn<Itree<noE, std::pair<Nat, crane::obj>>(Nat)>>(
              CategoryOps::template case_<crane::obj,
                                          crane::fn<crane::obj(crane::obj)>>(
                  [](const auto &, const auto &) { return crane::obj(); },
                  [](crane::obj, crane::obj, crane::obj, const auto &x1,
                     crane::fn<crane::obj(crane::obj)> x2) {
                    return [=](crane::obj _x0) -> crane::obj {
                      return Function::Case_sum1(
                          x1, crane::any_cast<IFun<crane::obj, crane::obj>>(x2),
                          _x0);
                    };
                  },
                  crane::obj(), crane::obj(), crane::obj(),
                  crane_erase_fn([](const GetE &a0)
                                     -> Monads::template stateT<
                                         Nat, crane_carrier_tc_73ef07e9f18b86f9,
                                         crane::obj> {
                    return h_get<crane::obj>(crane_convert<GetE>(a0));
                  }),
                  crane_erase_fn([](const IncE &a0)
                                     -> Monads::template stateT<
                                         Nat, crane_carrier_tc_73ef07e9f18b86f9,
                                         crane::obj> {
                    return h_inc<crane::obj>(crane_convert<IncE>(a0));
                  }))(Sum1<crane::obj, crane::obj, crane::obj>(x)))(x0));
    };
  }

  static inline const Itree<noE, std::pair<Nat, Nat>> out =
      State::template interp_state<MonadIter_itree<noE>, Monad_itree<noE>,
                                   Functor_itree<noE>,
                                   Sum1<GetE, IncE, crane::obj>, Nat, Nat>(
          [](const auto &a0)
              -> Monads::template stateT<Nat, crane_carrier_tc_73ef07e9f18b86f9,
                                         crane::obj> {
            return h<crane::obj>(
                crane_convert<Sum1<GetE, IncE, crane::obj>>(a0));
          },
          prog)(Nat::o());
  static std::optional<std::pair<Nat, Nat>>
  run(const Nat &fuel, const Itree<noE, std::pair<Nat, Nat>> &t);
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
      auto _lit3 = Nat::s(Nat::s(
          Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(
              Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(
                  Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(
                      Nat::s(std::move(_lit2)))))))))))))))))))))))))))))));
      auto _lit4 = Nat::s(Nat::s(
          Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(
              Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(
                  Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(
                      Nat::s(std::move(_lit3)))))))))))))))))))))))))))))));
      auto _lit5 = Nat::s(Nat::s(
          Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(
              Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(
                  Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(
                      Nat::s(std::move(_lit4)))))))))))))))))))))))))))))));
      return run(
          Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(
              Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(
                  Nat::s(Nat::s(Nat::s(std::move(_lit5))))))))))))))))))))),
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
typename _tcI0::template F<T3>
Functor0::fmap(F0 &&x, typename _tcI0::template F<T2> x0) {
  return _tcI0::template fmap<T2, T3>(x, std::move(x0));
}

template <Monad _tcI0, typename T2>
typename _tcI0::template m<T2> Monad0::ret(const T2 &x) {
  return _tcI0::template ret<T2>(x);
}

template <Monad _tcI0, typename T2, typename T3, typename F1>
typename _tcI0::template m<T3> Monad0::bind(typename _tcI0::template m<T2> x,
                                            F1 &&x0) {
  return _tcI0::template bind<T2, T3>(std::move(x), x0);
}

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
T2 CategoryOps::case_(F0 &&, std::type_identity_t<Case<T1, T2>> case0,
                      const T1 &x0_, const T1 &x1_, const T1 &x2_,
                      const T2 &x3_, T2 x4_) {
  return case0(x0_, x1_, x2_, x3_, std::move(x4_));
}

template <typename T1, typename T2, typename F0>
T2 CategoryOps::inl_(F0 &&, std::type_identity_t<Inl<T1, T2>> inl0,
                     const T1 &x0_, T1 x1_) {
  return inl0(x0_, std::move(x1_));
}

template <typename T1, typename T2, typename F0>
T2 CategoryOps::inr_(F0 &&, std::type_identity_t<Inr<T1, T2>> inr0,
                     const T1 &x0_, T1 x1_) {
  return inr0(x0_, std::move(x1_));
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
  requires std::is_invocable_r_v<T1, F0 &, const T1 &, const T1 &>
ReSum<T1, T2>
CategoryOps::ReSum_inl(F0 &&bif, std::type_identity_t<Cat<T1, T2>> h0,
                       std::type_identity_t<Inl<T1, T2>> h2, const T1 &a,
                       const T1 &b, const T1 &c, T2 h4) {
  return CategoryOps::template cat<T1, T2>(
      std::move(h0), a, b, bif(b, c),
      CategoryOps::template resum<T1, T2>(a, b, std::move(h4)),
      CategoryOps::template inl_<T1, T2>(bif, std::move(h2), b, c));
}

template <typename T1, typename T2, typename F0>
  requires std::is_invocable_r_v<T1, F0 &, const T1 &, const T1 &>
ReSum<T1, T2>
CategoryOps::ReSum_inr(F0 &&bif, std::type_identity_t<Cat<T1, T2>> h0,
                       std::type_identity_t<Inr<T1, T2>> h3, const T1 &a,
                       const T1 &b, const T1 &c, T2 h4) {
  return CategoryOps::template cat<T1, T2>(
      std::move(h0), a, b, bif(c, b),
      CategoryOps::template resum<T1, T2>(a, b, std::move(h4)),
      CategoryOps::template inr_<T1, T2>(bif, std::move(h3), c, b));
}

template <typename T1, typename T2, typename T4, typename F0, typename F1>
std::invoke_result_t<F0 &, crane::rebind_t<T1, T4> &>
Function::case_sum1(F0 &&f, F1 &&g, const Sum1<T1, T2, T4> &ab) {
  if (std::holds_alternative<typename Sum1<T1, T2, T4>::Inl1>(ab.v())) {
    const auto &[a0] = std::get<typename Sum1<T1, T2, T4>::Inl1>(ab.v());
    return f(a0);
  } else {
    const auto &[a0] = std::get<typename Sum1<T1, T2, T4>::Inr1>(ab.v());
    return g(a0);
  }
}

template <typename T1, typename T2, typename T3>
crane::rebind_t<T2, T3>
Subevent::subevent(ReSum<crane::obj, IFun<crane::obj, crane::obj>> h0,
                   crane::rebind_t<T1, T3> x) {
  return crane_any_cast<crane::rebind_t<T2, T3>>(
      CategoryOps::resum(crane::obj(), crane::obj(), h0)(std::move(x)));
}

template <MonadIter _tcI0, Monad _tcI1, Functor _tcI2, typename T1, typename T3>
typename _tcI0::template M<T3> Interp::interp(
    std::type_identity_t<crane::fn<typename _tcI0::template M<crane::obj>(T1)>>
        h0,
    Itree<T1, T3> x0_) {
  return _tcI0::template iter<T3, Itree<T1, T3>>(
      [=, h0 = std::move(h0)](const Itree<T1, T3> &t) ->
      typename _tcI0::template M<Sum<Itree<T1, T3>, T3>> {
        auto &&_sv = t.observe();
        if (std::holds_alternative<
                typename ItreeF<T1, T3, Itree<T1, T3>>::RetF>(_sv.v())) {
          const auto &[r0] =
              std::get<typename ItreeF<T1, T3, Itree<T1, T3>>::RetF>(_sv.v());
          return Monad0::template ret<_tcI1, Sum<Itree<T1, T3>, T3>>(
              Sum<Itree<T1, T3>, T3>::inr(r0));
        } else if (std::holds_alternative<
                       typename ItreeF<T1, T3, Itree<T1, T3>>::TauF>(_sv.v())) {
          const auto &[t1] =
              std::get<typename ItreeF<T1, T3, Itree<T1, T3>>::TauF>(_sv.v());
          return Monad0::template ret<_tcI1, Sum<Itree<T1, T3>, T3>>(
              Sum<Itree<T1, T3>, T3>::inl(t1));
        } else {
          const auto &[x, e0] =
              std::get<typename ItreeF<T1, T3, Itree<T1, T3>>::VisF>(_sv.v());
          return Functor0::template fmap<_tcI2, crane::obj,
                                         Sum<Itree<T1, T3>, T3>>(
              [=](const auto &x0) {
                return Sum<Itree<T1, T3>, T3>::inl(e0(x0));
              },
              h0(x));
        }
      },
      x0_);
}

template <MonadIter _tcI0, Monad _tcI1, Functor _tcI2, typename T1, typename T3,
          typename T4>
Monads::template stateT<T3, _tcI0::template M, T4> State::interp_state(
    std::type_identity_t<crane::fn<
        Monads::template stateT<T3, _tcI0::template M, crane::obj>(T1)>>
        h0,
    Itree<T1, T4> x) {
  return [=, h0 = std::move(h0)](const T3 &x0) {
    return crane_any_cast<typename _tcI0::template M<std::pair<T3, T4>>>(
        Interp::template interp<MonadIter_stateT0<_tcI1, _tcI0, T3>,
                                Monads::template Monad_stateT<_tcI1, T3>,
                                Monads::template Functor_stateT<_tcI2, T3>, T1,
                                T4>(h0, x)(x0));
  };
}

#endif // INCLUDED_INTERP_STATE_CASE_HANDLER
