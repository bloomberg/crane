#include "prop_erasure.h"

unsigned int PropErasure::with_proof_arg(unsigned int n) { return n; }

unsigned int PropErasure::add_with_proof(unsigned int _x0, unsigned int _x1) {
  return (_x0 + _x1);
}
