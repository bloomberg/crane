#include "tc_method_arity_mismatch.h"

uint64_t TcMethodArityMismatch::run(uint64_t k) {
  return useit<TcMethodArityMismatch::MkNat>((k + UINT64_C(2)));
}
