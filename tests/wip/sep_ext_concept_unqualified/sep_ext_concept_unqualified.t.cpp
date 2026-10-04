// Expected failure: SepExtConceptUnqualified.h:8 uses the concept `Params`
// unqualified in a template parameter constraint ("template <Params _tcI0>"),
// instead of `ParamsDef::Params` -- a compile error ("unknown type name
// 'Params'"), even though the ordinary type uses on the same line
// (ParamsDef::prov) are correctly qualified. Separate extraction wraps each
// source file in its own namespace; whatever qualifies identifiers in
// ordinary type/value positions is not being applied to a typeclass name
// used as a template-parameter constraint.
#include "ParamsDef.h"
#include "SepExtConceptUnqualified.h"

#include <cassert>

struct AnyParams {
  static ParamsDef::Provenance PROV() { return ParamsDef::Provenance::BUILD_PROVENANCE; }
};

int main() {
  ParamsDef::prov x{};
  assert((SepExtConceptUnqualified::use_it<AnyParams>(x), true));
  return 0;
}
