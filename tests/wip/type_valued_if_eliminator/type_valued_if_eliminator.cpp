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
    return x;
  } else {
    return x.length();
  }
}
