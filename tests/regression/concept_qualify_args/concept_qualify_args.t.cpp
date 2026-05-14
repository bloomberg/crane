#include "concept_qualify_args.h"

#include <cassert>

int main() {
  // Test that concept body correctly qualifies type args (typename M::t)
  assert(ConceptQualifyArgs::NatElems::head_or(42u) == 1u);
  assert(ConceptQualifyArgs::UseNatElems::first_or_default(0u) == 1u);

  return 0;
}
