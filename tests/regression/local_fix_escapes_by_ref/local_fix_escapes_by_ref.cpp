#include "local_fix_escapes_by_ref.h"

/// map_monad_acc (Vellvm's ListUtil.map_monad_acc) is a local fix
/// whose recursive call sits in a bind continuation.  Crane emitted the
/// fix as auto loop_impl = [&](auto &_self_loop, ...) { ... f(a0) ... }
/// and the continuation as [=](T3 b) { return _self_loop(_self_loop, ...);
/// }, which copied loop_impl -- still holding f and the enclosing frame
/// {e by reference} -- into a closure that escapes.  In a state monad the
/// bind does not run the continuation; it returns a function of the state,
/// which is called after map_monad_acc has returned, by when f is a
/// dangling reference.  The fixpoint's escape analysis looked only at the
/// code after the fixpoint, never inside its own bodies, and not at all
/// when the fixpoint is applied where it is defined.  A self-call inside a
/// closure the fixpoint's body builds now makes the fixpoint capture by
/// value.
///
/// check alone can pass, because the dead frame is often still intact;
/// the test driver also builds the state function, overwrites the stack,
/// and only then runs it.
///
/// Found in Vellvm's mem-scan and alloca-churn (Memory1's state monad
/// memS).
/// Each step doubles the element and counts one state tick.
LocalFixEscapesByRef::res<List<uint64_t>>
LocalFixEscapesByRef::run(const List<uint64_t> &l) {
  return map_monad_acc<uint64_t, uint64_t>(
             [](uint64_t x) {
               return st<uint64_t>{[=](uint64_t s) {
                 return res<uint64_t>::res0((s + 1), (UINT64_C(2) * x));
               }};
             },
             l)
      .runst(UINT64_C(0));
}

bool LocalFixEscapesByRef::check(std::monostate) {
  const auto &_sv = run(List<uint64_t>::cons(
      UINT64_C(1),
      List<uint64_t>::cons(
          UINT64_C(2),
          List<uint64_t>::cons(
              UINT64_C(3),
              List<uint64_t>::cons(UINT64_C(4), List<uint64_t>::nil())))));
  const auto &[s, a] = _sv;
  return (s == UINT64_C(4) && a.template fold_left<uint64_t>(
                                  [](uint64_t _x0, uint64_t _x1) -> uint64_t {
                                    return (_x0 + _x1);
                                  },
                                  UINT64_C(0)) == UINT64_C(20));
}
