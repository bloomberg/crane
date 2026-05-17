#include "prop_erasure.h"

uint64_t PropErasure::with_proof_arg(uint64_t n) { return n; }

uint64_t PropErasure::add_with_proof(uint64_t _x0, uint64_t _x1) {
  return (_x0 + _x1);
}
