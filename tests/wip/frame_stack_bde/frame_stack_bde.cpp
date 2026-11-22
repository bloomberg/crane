#include "frame_stack_bde.h"

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

unsigned int FrameStackBde::sum(const List<unsigned int> &l) {
  if (bsl::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
    return 0u;
  } else {
    const auto &[d_a0, d_a1] =
        bsl::get<typename List<unsigned int>::Cons>(l.v());
    return (d_a0 + sum(*d_a1));
  }
}
