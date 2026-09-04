#include "type_valued_if_eliminator.h"

TypeValuedIfEliminator::sel TypeValuedIfEliminator::zero(bool b) {
  if (b) {
    return Nat::o();
  } else {
    return List<std::any>::nil();
  }
}

Nat TypeValuedIfEliminator::size(bool b, TypeValuedIfEliminator::sel x) {
  if (b) {
    return std::any_cast<Nat>(x);
  } else {
    return List<Nat>(std::any_cast<List<std::any>>(x)).length();
  }
}
