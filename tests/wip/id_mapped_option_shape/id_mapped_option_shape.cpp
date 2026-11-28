#include "id_mapped_option_shape.h"

uint64_t IdMappedOptionShape::fo(std::optional<uint64_t> o) {
  if (o.has_value()) {
    const uint64_t &k = *o;
    return k;
  } else {
    return UINT64_C(2);
  }
}

crane::obj Datatypes::id(crane::obj x) { return x; }
