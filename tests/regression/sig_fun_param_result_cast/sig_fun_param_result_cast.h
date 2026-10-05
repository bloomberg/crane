#ifndef INCLUDED_SIG_FUN_PARAM_RESULT_CAST
#define INCLUDED_SIG_FUN_PARAM_RESULT_CAST

#include "crane_fn.h"
#include "fn.h"
#include "obj.h"
#include <cstdint>
#include <utility>
#include <variant>

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

/// A sig whose payload is a function, passed as a parameter (so its C++ type
/// is the concrete Sig<std::function<uint64_t(uint64_t)>>), must be applied
/// directly rather than through an erased-function cast.
struct SigFunParamResultCast {
  static uint64_t apply_sig(const Sig<crane::fn<uint64_t(uint64_t)>> &f,
                            uint64_t n);
  static inline const Sig<crane::fn<uint64_t(uint64_t)>> idf =
      Sig<crane::fn<uint64_t(uint64_t)>>::exist([](uint64_t n) { return n; });
  static constexpr uint64_t go = UINT64_C(2);
};

#endif // INCLUDED_SIG_FUN_PARAM_RESULT_CAST
