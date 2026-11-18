#include "unused_let_local_fix_werror.h"

/// Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
/// testing of Crane: a generated program, shrunk by ephyra and reduced by hand.
///
/// A let bound to a local fixpoint's result, read only in the never-taken
/// recursive arm of another local fixpoint that is called on []: the arm is
/// dropped but the binding is kept, "variable 'x' set but not used" under
/// -Werror.  The value is right.  go2's loop drops its unread acc, and
/// with it the only read of x; the declaration and the assignment of the
/// choice x's value was lowered to stayed.  Simplify now drops a local
/// declared without a value that nothing reads, with the pure values,
/// choices among them included, assigned to it.
uint64_t UnusedLetLocalFixWerror::f(uint64_t) {
  List<uint64_t> l = List<uint64_t>::nil();
  {
    const List<bool> &_lc1_l0 = List<bool>::nil();
    // Loop replaces the tail recursion: each recursive call updates the loop
    // variables.
    const List<bool> *_lc1_loop_l0 = &_lc1_l0;
    while (true) {
      if (std::holds_alternative<typename List<bool>::Nil>(_lc1_loop_l0->v())) {
        return UINT64_C(0);
      } else {
        const auto &[_, a10] =
            std::get<typename List<bool>::Cons>(_lc1_loop_l0->v());
        _lc1_loop_l0 = crane_raw(a10);
      }
    }
  }
}
