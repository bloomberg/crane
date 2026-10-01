#include "type_valued_if_eliminator.h"

TypeValuedIfEliminator::sel TypeValuedIfEliminator::zero(bool b) {
  if (b) {
    return Nat::o();
  } else {
    return List<crane::obj>::nil();
  }
}

Nat TypeValuedIfEliminator::size(bool b, TypeValuedIfEliminator::sel x) {
  if (b) {
    return crane::any_cast<Nat>(std::move(x));
  } else {
    return List<Nat>(crane::any_cast<List<crane::obj>>(x)).length();
  }
}
