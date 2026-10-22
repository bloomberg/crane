#include "loopify_shadow_in_scrutinee_call.h"

/// A tail loop matching on a call that takes its parameters.
///
/// The loop walks n and xs by pointer (const Nat *_loop_n), and reads
/// them through the pointer.  A scrutinee that mentions a pointer was taken
/// for the pointer itself, so firstn n xs was passed the pointers, which
/// did not compile.
Nat LoopifyShadowInScrutineeCall::walk(const Nat &n, const List<Nat> &xs,
                                       Nat acc) {
  Nat _loop_acc = std::move(acc);
  const Nat *_loop_n = &n;
  while (true) {
    if (std::holds_alternative<typename Nat::O>(_loop_n->v())) {
      return _loop_acc;
    } else {
      const auto &[a0] = std::get<typename Nat::S>(_loop_n->v());
      auto &&_sv0 = xs.firstn(*_loop_n);
      if (std::holds_alternative<typename List<Nat>::Nil>(_sv0.v())) {
        _loop_n = crane_raw(a0);
      } else {
        const auto &[a00, a10] = std::get<typename List<Nat>::Cons>(_sv0.v());
        _loop_acc = _loop_acc.add(a00);
        _loop_n = crane_raw(a0);
      }
    }
  }
}
