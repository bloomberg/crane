#include "nested_match_unreachable_bde.h"

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

bool NestedMatchUnreachableBde::same(Comparison c, Comparison d) {
  switch (c) {
  case Comparison::e_EQ: {
    switch (d) {
    case Comparison::e_EQ: {
      return true;
    }
    default: {
      return false;
    }
    }
    break;
  }
  case Comparison::e_LT: {
    switch (d) {
    case Comparison::e_LT: {
      return true;
    }
    default: {
      return false;
    }
    }
    break;
  }
  case Comparison::e_GT: {
    switch (d) {
    case Comparison::e_GT: {
      return true;
    }
    default: {
      return false;
    }
    }
    break;
  }
  default:
    std::unreachable();
  }
}
