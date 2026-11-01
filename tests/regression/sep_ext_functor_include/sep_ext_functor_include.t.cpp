// A functor constrained by a module type of another file, applying a functor
// of that file in its body: the header names Ord:: only around declarations,
// so it must include Ord.h for itself.  Included first, it is on its own.
#include "SepExtFunctorInclude.h"

#include <cassert>

int main() {
  assert(SepExtFunctorInclude::gt_two_one);
  return 0;
}
