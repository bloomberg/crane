#include "loopify_receiver_from_temporary.h"

/// A tail-recursive method whose recursive call passes, as the receiver, a
/// binder of a match on a value the turn makes.
///
/// The loop keeps the receiver as a pointer, _loop_self.  A receiver made
/// in the turn must be parked in a local outliving the loop first, and the
/// C++ reading that decided this saw only receivers spelled as temporaries:
/// inner is a reference into the result of wrap, so the loop pointed at
/// it, and the next turn read it after that result was destroyed -- a
/// heap-use-after-free.  The turns whose receiver no parameter of the loop
/// gives are now the recursion plan's ({!Control_ir.rebuilt}), and these
/// park.
uint64_t LoopifyReceiverFromTemporary::go(uint64_t n) {
  return t::l().walk(n, UINT64_C(0));
}
