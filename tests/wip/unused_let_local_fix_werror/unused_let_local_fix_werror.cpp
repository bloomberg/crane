#include "unused_let_local_fix_werror.h"

/// Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
/// testing of Crane: a generated program, shrunk by ephyra and reduced by hand.
///
/// A let bound to a local fixpoint's result, read only in the never-taken
/// recursive arm of another local fixpoint that is called on []: the arm is
/// dropped but the binding is kept, "variable 'x' set but not used" under
/// -Werror.  The value is right.
uint64_t UnusedLetLocalFixWerror::f(uint64_t) {
  uint64_t x;
  List<uint64_t> l = List<uint64_t>::nil();
  x = (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())
           ? UINT64_C(0)
           : UINT64_C(7));
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
