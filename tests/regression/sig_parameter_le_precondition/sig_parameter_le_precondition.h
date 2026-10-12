#ifndef INCLUDED_SIG_PARAMETER_LE_PRECONDITION
#define INCLUDED_SIG_PARAMETER_LE_PRECONDITION

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

struct SigParameterLePrecondition {
  static uint64_t get(uint64_t _x, const Sig<uint64_t> &b);
  static uint64_t get2(uint64_t _x, const Sig<uint64_t> &b);
  static inline const uint64_t result =
      (get(UINT64_C(5), Sig<uint64_t>::exist(UINT64_C(3))) +
       get2(UINT64_C(0), Sig<uint64_t>::exist(UINT64_C(2))));
};

#endif // INCLUDED_SIG_PARAMETER_LE_PRECONDITION
