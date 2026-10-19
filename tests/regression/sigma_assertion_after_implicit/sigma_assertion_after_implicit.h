#ifndef INCLUDED_SIGMA_ASSERTION_AFTER_IMPLICIT
#define INCLUDED_SIGMA_ASSERTION_AFTER_IMPLICIT

#include "crane_fn.h"
#include "obj.h"
#include <cassert>
#include <cstdint>
#include <stdexcept>
#include <utility>
#include <variant>

template <typename A> struct Sig;

template <typename A> struct Sig {
  // DATA
  A x;

  // ACCESSORS
  Sig<A> clone() const { return {x}; }

  template <typename CraneU> operator Sig<CraneU>() const {
    return {[&]() -> CraneU {
      if constexpr (crane_convertible<CraneU, const A &>) {
        return crane_convert<CraneU>(x);
      } else {
        throw std::logic_error(
            "unreachable: inactive constructor field at this instantiation");
      }
    }()};
  }

  // CREATORS
  static Sig<A> exist(A x) { return {std::move(x)}; }
};

struct SigmaAssertionAfterImplicit {
  static uint64_t f(const Sig<uint64_t> &x, const Sig<uint64_t> &y);
  static inline const uint64_t test =
      f(Sig<uint64_t>::exist(UINT64_C(7)), Sig<uint64_t>::exist(UINT64_C(1)));
};

#endif // INCLUDED_SIGMA_ASSERTION_AFTER_IMPLICIT
