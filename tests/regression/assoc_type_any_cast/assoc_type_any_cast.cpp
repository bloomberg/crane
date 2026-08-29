#include "assoc_type_any_cast.h"

uint64_t AssocTypeAnyCast::run(uint64_t k) {
  return roundtrip<AssocTypeAnyCast::PairWrap>((k + UINT64_C(5)));
}
