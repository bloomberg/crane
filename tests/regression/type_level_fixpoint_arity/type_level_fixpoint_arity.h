#ifndef INCLUDED_TYPE_LEVEL_FIXPOINT_ARITY
#define INCLUDED_TYPE_LEVEL_FIXPOINT_ARITY

#include "crane_fn.h"
#include <any>
#include <functional>

struct TypeLevelFixpointArity {
  /// A type computed by a fixpoint over a nat loses its arity, so values
  /// built at one arity are read back at another.
  using nfun = std::any;
  static nfun constN(uint64_t n, uint64_t v);
  static uint64_t apply1(nfun f, uint64_t x);
  static uint64_t apply2(nfun f, uint64_t x, uint64_t y);
  static inline const uint64_t total =
      ((std::any_cast<uint64_t>(constN(UINT64_C(0), UINT64_C(7))) +
        apply1(constN(UINT64_C(1), UINT64_C(8)), UINT64_C(0))) +
       apply2(constN(UINT64_C(2), UINT64_C(9)), UINT64_C(0), UINT64_C(0)));
};

#endif // INCLUDED_TYPE_LEVEL_FIXPOINT_ARITY
