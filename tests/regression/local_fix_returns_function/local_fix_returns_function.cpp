#include "local_fix_returns_function.h"

/// Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
/// testing of Crane: a generated program, shrunk by ephyra and reduced by hand.
///
/// A local let fix go ... : nat -> nat applied to one more argument than it
/// binds.  The C++ lambda for go is eta-expanded to return uint64_t, but its
/// branches still return lambdas, and the recursive call names go inside its
/// own auto initializer.  Under CRANE_CHECK_IR=1 (the test suite) extraction
/// stops first: "closure escape: the local fixpoint go escapes in its
/// generated code but nowhere in Core".
uint64_t LocalFixReturnsFunction::t(const List<uint64_t> &l) {
  {
    const List<uint64_t> &_lc1_l0 = l;
    const crane::fn<uint64_t(uint64_t)> &_lc1_acc =
        [](uint64_t x) { return x; };
    uint64_t _lc1_x0_ = UINT64_C(1);
    // Loop replaces the tail recursion: each recursive call updates the loop
    // variables.
    const List<uint64_t> *_lc1_loop_l0 = &_lc1_l0;
    while (true) {
      if (std::holds_alternative<typename List<uint64_t>::Nil>(
              _lc1_loop_l0->v())) {
        return (_lc1_x0_ + UINT64_C(1));
      } else {
        const auto &[_, a1] =
            std::get<typename List<uint64_t>::Cons>(_lc1_loop_l0->v());
        _lc1_loop_l0 = crane_raw(a1);
      }
    }
  }
}
