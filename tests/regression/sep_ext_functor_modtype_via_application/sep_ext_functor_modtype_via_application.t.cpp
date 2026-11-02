// A module type a functor of another file declares, reached through an
// application of the functor: the header names Inner::F_S over the
// application's argument.  Included first, it is on its own.
#include "SepExtFunctorModtypeViaApplication.h"

#include <cassert>

int main() {
  assert(SepExtFunctorModtypeViaApplication::res);
  return 0;
}
