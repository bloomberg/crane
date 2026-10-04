#include "let_polymorphic_lift_rename.h"

/// A let-bound polymorphic function is lifted out of the body into a template,
/// but only the *first* use is rewritten to the lifted name: the second and
/// later uses still say id2, which no longer exists.  The number of type
/// instantiations is irrelevant — what matters is that the binder is used more
/// than once.
Nat LetPolymorphicLiftRename::body(const Nat &n) {
  return body_crane_id2(n).add([]() {
    switch (body_crane_id2(Bool0::TRUE_)) {
    case Bool0::TRUE_: {
      return Nat::s(Nat::o());
    }
    case Bool0::FALSE_: {
      return Nat::o();
    }
    default:
      std::unreachable();
    }
  }());
}
