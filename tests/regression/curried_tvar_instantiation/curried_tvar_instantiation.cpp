#include "curried_tvar_instantiation.h"

/// A type variable instantiated at a curried function type is spelled
/// std::function<Nat(Nat,Nat)> (flattened) in one place and
/// std::function<std::function<Nat(Nat)>(Nat)> (curried) in the other, so the
/// declaration and the call site disagree.
Nat CurriedTvarInstantiation::ex(const Nat &x0_) {
  static const auto apply_all_1 =
      crane::immortal(apply_all<crane::fn<Nat(Nat)>>(
          List<crane::fn<crane::fn<Nat(Nat)>(crane::fn<Nat(Nat)>)>>::cons(
              [](crane::fn<Nat(Nat)> g) { return g; },
              List<crane::fn<crane::fn<Nat(Nat)>(crane::fn<Nat(Nat)>)>>::nil()),
          [](const Nat &x) { return Nat::s(x); }));
  return apply_all_1(x0_);
}
