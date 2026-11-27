#include "bool_dec_bde.h"

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

bool BoolDecBde::eqb_dec(bool a, bool b) {
  if (Bool::bool_dec(a, b)) {
    return true;
  } else {
    return false;
  }
}

bool Bool::bool_dec(bool b1, bool b2) {
  if (b1) {
    if (b2) {
      return true;
    } else {
      return false;
    }
  } else if (b2) {
    return false;
  } else {
    return true;
  }
}
