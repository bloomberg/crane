#include "functor_modtype_via_application.h"

/// A module type declared in a functor's body, reached through an
/// application of the functor: G.S is the functor's concept F_S over
/// the application's argument, not a member of G.
Nat FunctorModtypeViaApplication::YY::f(bool b) {
  if (b) {
    return Nat::s(Nat::o());
  } else {
    return Nat::o();
  }
}
