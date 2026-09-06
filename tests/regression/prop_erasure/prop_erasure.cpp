#include "prop_erasure.h"

uint64_t PropErasure::with_proof_arg(uint64_t n) { return n; }

uint64_t PropErasure::add_with_proof(uint64_t x0_, uint64_t x1_) {
  return (x0_ + x1_);
}
