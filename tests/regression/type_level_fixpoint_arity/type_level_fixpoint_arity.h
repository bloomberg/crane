#ifndef INCLUDED_TYPE_LEVEL_FIXPOINT_ARITY
#define INCLUDED_TYPE_LEVEL_FIXPOINT_ARITY

#include "crane_fn.h"
#include "fn.h"
#include "obj.h"
#include <cstdint>
#include <functional>
#include <utility>

struct TypeLevelFixpointArity {
  /// A type computed by a fixpoint over a nat loses its arity, so values
  /// built at one arity are read back at another.
  using nfun = crane::obj;
  static nfun constN(uint64_t n, uint64_t v);
  static uint64_t apply1(nfun f, uint64_t x);
  static uint64_t apply2(nfun f, uint64_t x, uint64_t y);
  static constexpr uint64_t total = UINT64_C(24);
};

#endif // INCLUDED_TYPE_LEVEL_FIXPOINT_ARITY
