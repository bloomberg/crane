#ifndef INCLUDED_FUNCTOR_PARAM_SIGNATURE_TYPE
#define INCLUDED_FUNCTOR_PARAM_SIGNATURE_TYPE

#include "crane_fn.h"
#include "obj.h"
#include <concepts>
#include <stdexcept>
#include <utility>
#include <variant>

template <typename A, typename P> struct SigT;

template <typename A, typename P> struct SigT {
  // DATA
  A x;
  P a1;

  // ACCESSORS
  SigT<A, P> clone() const { return {x, a1}; }

  template <typename CraneU0, typename CraneU1>
  operator SigT<CraneU0, CraneU1>() const {
    return {[&]() -> CraneU0 {
              if constexpr (crane_convertible<CraneU0, const A &>) {
                return crane_convert<CraneU0>(x);
              } else {
                throw std::logic_error("unreachable: inactive constructor "
                                       "field at this instantiation");
              }
            }(),
            [&]() -> CraneU1 {
              if constexpr (crane_convertible<CraneU1, const P &>) {
                return crane_convert<CraneU1>(a1);
              } else {
                throw std::logic_error("unreachable: inactive constructor "
                                       "field at this instantiation");
              }
            }()};
  }

  // CREATORS
  static SigT<A, P> existt(A x, P a1) { return {std::move(x), std::move(a1)}; }
};

template <typename M>
concept SymbolTypes = requires {
  typename M::terminal;
  {
    M::eqT(std::declval<typename M::terminal>(),
           std::declval<typename M::terminal>())
  } -> std::same_as<bool>;
  typename M::semty;
};
template <typename M>
concept DefsT = requires {
  {
    M::t_eq_dec(std::declval<typename M::TA::t>(),
                std::declval<typename M::TA::t>())
  } -> std::same_as<bool>;
};
template <typename M>
concept T = requires { requires SymbolTypes<typename M::SymTy>; };

struct FunctorParamSignatureType {
  template <SymbolTypes Ty> struct DefsFn {
    struct TA {
      using t = typename Ty::terminal;

      static bool eq_dec(t x0_, t x1_) {
        return Ty::eqT(std::move(x0_), std::move(x1_));
      }
    };

    static bool t_eq_dec(typename TA::t x0_, typename TA::t x1_) {
      return TA::eq_dec(std::move(x0_), std::move(x1_));
    }
  };

  template <T D> struct UseFn {
    static bool same(const SigT<typename D::SymTy::terminal, crane::obj> &t0,
                     typename D::SymTy::terminal a) {
      const auto &[x, a1] = t0;
      if (D::Defs::t_eq_dec(crane::any_cast<typename D::Defs::TA::t>(x),
                            std::move(a))) {
        return true;
      } else {
        return false;
      }
    }
  };
};

#endif // INCLUDED_FUNCTOR_PARAM_SIGNATURE_TYPE
