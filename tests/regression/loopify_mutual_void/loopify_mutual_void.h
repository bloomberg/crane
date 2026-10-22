#ifndef INCLUDED_LOOPIFY_MUTUAL_VOID
#define INCLUDED_LOOPIFY_MUTUAL_VOID

#include <cstdint>
#include <variant>

/// Mutual recursion between functions returning nothing.
///
/// A tail call of odd_void is generated as its statement and a return,
/// odd_void(m); return;, which Loopify did not continue in: it ran the
/// partner's body in a lambda, declared a machine with a void _result
/// and called an adopted entry it never defined, and the C++ did not
/// compile.  The call now continues in the partner's body, every path of
/// which ends in a return, and the group is a tail loop.
struct LoopifyMutualVoid {
  static void even_void(uint64_t n);
  static void odd_void(uint64_t n);
};

#endif // INCLUDED_LOOPIFY_MUTUAL_VOID
