// A functor parameter constrained by a module type that a functor's body
// declares, reached through an application of that functor: the constraint
// is the functor's concept over the application's argument.
#include "functor_modtype_via_application.h"

#include <cassert>

int main() {
  assert(FunctorModtypeViaApplication::res);
  return 0;
}
