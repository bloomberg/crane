// A typeclass concept used as a template-parameter constraint in another
// file's header.  Separate extraction wraps each source file in its own
// namespace; a concept is hoisted out of every enclosing struct but not out
// of its file's namespace, so the constraint must read
// `template <ParamsDef::Params _tcI0>`, qualified like the ordinary type uses
// (ParamsDef::prov) on the same line.
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
