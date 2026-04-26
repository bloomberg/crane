#include <prop_erasure.h>

#include <memory>
#include <optional>
#include <type_traits>

__attribute__((pure)) unsigned int PropErasure::with_proof_arg(unsigned int n) {
  return n;
}

__attribute__((pure)) unsigned int
PropErasure::add_with_proof(const unsigned int &_x0, const unsigned int &_x1) {
  return (_x0 + _x1);
}
