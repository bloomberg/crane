#ifndef INCLUDED_SIG_CURRIED_PAYLOAD
#define INCLUDED_SIG_CURRIED_PAYLOAD

#include "crane_fn.h"
#include "fn.h"
#include "obj.h"
#include <cstdint>
#include <utility>

template <typename A> struct Sig;

template <typename A> struct Sig {
  // DATA
  A x;

  // ACCESSORS
  Sig<A> clone() const { return {x}; }

  template <typename CraneU>
    requires crane_convertible<CraneU, const A &>
  operator Sig<CraneU>() const {
    return {crane_convert<CraneU>(x)};
  }

  // CREATORS
  static Sig<A> exist(A x) { return {std::move(x)}; }
};

struct SigCurriedPayload {
  static inline const Sig<crane::fn<uint64_t(uint64_t, uint64_t)>> mk =
      Sig<crane::fn<uint64_t(uint64_t, uint64_t)>>::exist(
          [](uint64_t _x0, uint64_t _x1) -> uint64_t { return (_x0 + _x1); });
  static constexpr uint64_t go = UINT64_C(3);
};

#endif // INCLUDED_SIG_CURRIED_PAYLOAD
