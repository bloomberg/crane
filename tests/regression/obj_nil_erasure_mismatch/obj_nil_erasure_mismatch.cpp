#include "obj_nil_erasure_mismatch.h"

/// Directly-callable copies of the two TOPSYM-shaped actions, so the C++
/// test driver can invoke the "cons" and "nil" cases individually and
/// observe the mismatched erased shapes.
std::deque<Prod<Nat, Nat>> top_cons_action(Unit) {
  return [](auto _a0, auto _a1) {
    _a1.push_front(_a0);
    return _a1;
  }(Prod<Nat, Nat>::pair(
             Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::o()))))))),
             Nat::s(Nat::s(
                 Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::o()))))))))),
         std::deque<Prod<Nat, Nat>>{});
}

std::deque<Prod<Nat, Nat>> top_nil_action(Unit) {
  return std::deque<Prod<Nat, Nat>>{};
}
