#include "bde_concept_declval_include.h"

#include <bsl_concepts.h>
#include <bsl_functional.h>
#include <bsl_iostream.h>
#include <bsl_memory.h>
#include <bsl_stdexcept.h>
#include <bsl_string.h>
#include <bsl_type_traits.h>
#include <bsl_variant.h>
#include <bsl_vector.h>

namespace BloombergLP {}

unsigned int BdeConceptDeclvalInclude::N::op(unsigned int x0_,
                                             unsigned int x1_) {
  return x0_ + x1_;
}
