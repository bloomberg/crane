#include "list_dep_type_erasure.h"

uint64_t ListDepTypeErasure::dlen(const ListDepTypeErasure::dyn &x) {
  return x.contents.length();
}
