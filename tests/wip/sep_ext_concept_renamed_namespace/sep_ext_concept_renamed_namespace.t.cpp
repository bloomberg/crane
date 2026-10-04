// Expected failure: SepExtConceptRenamedNamespace.h:9 qualifies the concept
// as `Foo::Foo`, matching the defining file's own name (Foo.v). But Foo.h
// puts the concept in `namespace Foo_` (suffixed), not `namespace Foo`,
// because the concept's own name ("Foo") collides with the file/module name
// ("Foo") that would otherwise be the namespace -- so the printer renames
// the namespace to avoid self-shadowing. The cross-file qualification fix
// (sep_ext_concept_unqualified) qualifies with the file's nominal name, not
// its possibly-renamed actual namespace, so this fails with "no member
// named 'Foo' in namespace 'Foo'" / "use of undeclared identifier".
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
