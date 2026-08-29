#include "assoc_type_tvar_leak.h"

uint64_t AssocTypeTvarLeak::run(uint64_t k) {
  return (go<AssocTypeTvarLeak::EN>() + k);
}
