#ifndef INCLUDED_LOOPIFY_INNER_INSTANCE_CALL
#define INCLUDED_LOOPIFY_INNER_INSTANCE_CALL

#include "crane_fn.h"
#include "fn.h"
#include "lazy.h"
#include "obj.h"
#include "shared_block.h"
#include "small_vector.h"
#include <atomic>
#include <concepts>
#include <cstdint>
#include <stdexcept>
#include <utility>
#include <variant>

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

struct Monads {
  template <typename s, template <typename> class m, typename a>
  using stateT = crane::fn<m<std::pair<s, a>>(s)>;

  template <Functor _tcI0, typename T1> struct Functor_stateT {
    template <typename CraneA0>
    using F = crane::fn<typename _tcI0::template F<std::pair<T1, CraneA0>>(T1)>;

    template <typename CraneA0, typename CraneA1>
    static crane::fn<typename _tcI0::template F<std::pair<T1, CraneA1>>(T1)>
    fmap(
        crane::fn<CraneA1(CraneA0)> f,
        crane::fn<typename _tcI0::template F<std::pair<T1, CraneA0>>(T1)> run) {
      return [=, f = std::move(f), run = std::move(run)](const T1 &s) {
        return _tcI0::template fmap<std::pair<T1, CraneA0>,
                                    std::pair<T1, CraneA1>>(
            [=](const std::pair<T1, CraneA0> &sa) {
              return std::make_pair(sa.first, f(sa.second));
            },
            run(s));
      };
    }
  };
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
        const Itree<T1, T2> &u) { /// CraneEnter: captures varying parameters
                                  /// for each recursive call.

    struct CraneEnter {
      Itree<T1, T2> u;
    };

    using CraneFrame = std::variant<CraneEnter>;
    Itree<T1, T3> _result{};
    crane::small_vector<CraneFrame> _stack;
    _stack.emplace_back(CraneEnter{u});
    /// Loopified subst: CraneEnter.
    while (!_stack.empty()) {
      CraneFrame _frame = std::move(_stack.back());
      _stack.pop_back();
      auto _f = std::move(std::get<CraneEnter>(_frame));
      const Itree<T1, T2> &u = _f.u;
      auto &&_sv = u.observe();
      if (std::holds_alternative<typename ItreeF<T1, T2, Itree<T1, T2>>::RetF>(
              _sv.v())) {
        const auto &[r0] =
            std::get<typename ItreeF<T1, T2, Itree<T1, T2>>::RetF>(_sv.v());
        _result = k(r0);
      } else if (std::holds_alternative<
                     typename ItreeF<T1, T2, Itree<T1, T2>>::TauF>(_sv.v())) {
        const auto &[t0] =
            std::get<typename ItreeF<T1, T2, Itree<T1, T2>>::TauF>(_sv.v());
        _result = Itree<T1, T3>::lazy_([=]() -> typename Itree<T1, T3>::Go {
          return {[&]() {
            return ItreeF<T1, T3, Itree<T1, T3>>::tauf(
                subst<T1, T2, T3>(k, t0));
          }()};
        });
      } else {
        const auto &[x, e0] =
            std::get<typename ItreeF<T1, T2, Itree<T1, T2>>::VisF>(_sv.v());
        _result = Itree<T1, T3>::go(ItreeF<T1, T3, Itree<T1, T3>>::visf(
            x, crane::fn<Itree<T1, T3>(crane::obj)>(
                   [=](const crane::obj &x0) -> Itree<T1, T3> {
                     return subst<T1, T2, T3>(k, crane_call_erased(e0, x0));
                   })));
      }
    }
    return _result;
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
    return bind<T1, T2, T3>(t, [=](const T2 &x) {
      return Itree<T1, T3>::lazy_([=]() -> typename Itree<T1, T3>::Go {
        return {ItreeF<T1, T3, Itree<T1, T3>>::retf(f(x))};
      });
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

/// ITree's Functor_stateT is not recursive: its fmap calls the
/// *inner* functor's fmap.  With Set Crane Loopify it is nevertheless
/// loopified, as if that inner call were a self-call: the static method
/// Monads::Functor_stateT<...>::fmap gets a one-frame _Enter stack
/// starting with const Functor_stateT<_tcI0, T1> *_self = this;, and
/// this in a static member function does not compile ("invalid use of
/// 'this' outside of a non-static member function").  Monad_stateT's
/// bind gets the same treatment.
///
/// Found in Vellvm with the global Set Crane Loopify (3 of its 59
/// errors).  Even where it compiled, a call to another instance's method
/// treated as recursion would be a wrong program, not just a slow one.
struct LoopifyInnerInstanceCall {
  enum class Ev { ASK };
  template <typename CraneTcArg>
  using crane_carrier_tc_21402bc4025dedf3 = Itree<Ev, CraneTcArg>;
  static inline const Monads::template stateT<
      uint64_t, crane_carrier_tc_21402bc4025dedf3, uint64_t>
      st = [](uint64_t s) {
        return Monad_itree<Ev>::template ret<std::pair<uint64_t, uint64_t>>(
            std::make_pair(s, UINT64_C(41)));
      };
  static Itree<Ev, std::pair<uint64_t, uint64_t>> bumped(std::monostate _x);
  /// 5 is the state, 41 + 1 the value.
  static Itree<Ev, bool> check(std::monostate _x);
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

#endif // INCLUDED_LOOPIFY_INNER_INSTANCE_CALL
