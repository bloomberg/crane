// A partial application of a functor's member, eta-expanded against its
// callee's signature, whose return type names an alias declared in another
// file.
#include "Datatypes.h"
#include "ListDef.h"
#include "Lib.h"
#include "Inst.h"
#include "SepExtCalleeAliasTypeHead.h"

#include <cassert>

int main() {
  assert(SepExtCalleeAliasTypeHead::result == 3);
  return 0;
}
