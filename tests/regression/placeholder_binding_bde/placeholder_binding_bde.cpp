#include "placeholder_binding_bde.h"

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

unsigned int
PlaceholderBindingBde::middle(const PlaceholderBindingBde::tree &t) {
  if (bsl::holds_alternative<typename PlaceholderBindingBde::tree::Leaf>(t.v())) {
    return 0u;
  } else {
    const auto &[d_l, d_x, d_r] =
        bsl::get<typename PlaceholderBindingBde::tree::Node>(t.v());
    return d_x;
  }
}
