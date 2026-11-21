// A functor's nullary constant read through applications in two other
// files: the read calls its accessor.
#include "Datatypes.h"
#include "Pred.h"
#include "Sound.h"
#include "SepExtAccessorFunctorChain.h"

#include <cassert>

int main() {
  assert(SepExtAccessorFunctorChain::result == 3);
  return 0;
}
