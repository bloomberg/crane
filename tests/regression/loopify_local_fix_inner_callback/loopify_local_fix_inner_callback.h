#ifndef INCLUDED_LOOPIFY_LOCAL_FIX_INNER_CALLBACK
#define INCLUDED_LOOPIFY_LOCAL_FIX_INNER_CALLBACK

#include "small_vector.h"
#include <atomic>
#include <cstdint>
#include <utility>
#include <variant>

/// A local fixpoint whose recursive calls are all made by a fixpoint
/// inside it.
///
/// f calls itself only from ack_m, a fixpoint it applies in place.  A
/// machine for f leaves those calls where they are, in ack_m's
/// closure, but drops the self-parameter they recurse through, so the
/// loop it emitted named an undeclared _self_f.  A local machine does not
/// adopt an inner fixpoint as a second entry, so f is left recursing
/// natively.
struct LoopifyLocalFixInnerCallback {
  static uint64_t ack(const std::pair<uint64_t, uint64_t> &p);
  static inline const uint64_t small =
      ack(std::make_pair(UINT64_C(2), UINT64_C(3)));
};

#endif // INCLUDED_LOOPIFY_LOCAL_FIX_INNER_CALLBACK
