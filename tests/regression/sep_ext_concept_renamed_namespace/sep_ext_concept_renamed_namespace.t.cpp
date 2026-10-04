// A concept named like the file that defines it (class Foo in Foo.v).  A
// namespace may not share its name with a declaration directly inside it, so
// Foo.h emits `namespace Foo_`; a constraint in another file must spell the
// same renamed namespace, `template <Foo_::Foo _tcI0>`, and the file itself
// keeps its name (Foo.h).
#include "Datatypes.h"
#include "Foo.h"
#include "SepExtConceptRenamedNamespace.h"

#include <cassert>

struct AnyFoo {
  static Datatypes::Nat foo_val() { return Datatypes::Nat::o(); }
};

int main() {
  assert((SepExtConceptRenamedNamespace::use_it<AnyFoo>(), true));
  return 0;
}
