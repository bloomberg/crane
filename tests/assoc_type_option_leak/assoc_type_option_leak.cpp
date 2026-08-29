#include "assoc_type_option_leak.h"

uint64_t AssocTypeOptionLeak::run(uint64_t k) {
  return go<AssocTypeOptionLeak::OL>((k + UINT64_C(4)));
}
