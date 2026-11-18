#include "loopify_reread_loop_pointer.h"

/// Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
/// testing of Crane: a generated program, shrunk by ephyra and reduced by hand.
///
/// Under Loopify, a match on the loop variable nested inside a projection of
/// a match (py (match t with Leaf => fold_left ... | ...)) reads the loop
/// pointer as _loop_t.v() instead of _loop_t->v(): "member reference
/// type 'const tree *' is a pointer".  Fine without Loopify, and fine when
/// the fold_left is replaced by a plain record.  The tail loop set the
/// inner match's access to -> and left its expression t.v(), which the
/// conditional the match is lowered to reads.
bool LoopifyRereadLoopPointer::g(const LoopifyRereadLoopPointer::tree &t) {
  // Loop replaces the tail recursion: each recursive call updates the loop
  // variables.
  const LoopifyRereadLoopPointer::tree *_loop_t = &t;
  while (true) {
    if (std::holds_alternative<typename LoopifyRereadLoopPointer::tree::Leaf>(
            _loop_t->v())) {
      return (
          std::holds_alternative<typename LoopifyRereadLoopPointer::tree::Leaf>(
              _loop_t->v()) ? List<bool>::nil().template fold_left<
                                  LoopifyRereadLoopPointer::pt>(
                                  [](LoopifyRereadLoopPointer::pt acc,
                                     bool) { return acc; },
                                  pt{UINT64_C(0), true})
                            : pt{UINT64_C(0), false})
                 .py;
    } else {
      const auto &[a0, _, _] =
          std::get<typename LoopifyRereadLoopPointer::tree::Node>(_loop_t->v());
      _loop_t = crane_raw(a0);
    }
  }
}
