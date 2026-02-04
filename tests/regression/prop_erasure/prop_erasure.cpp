#include <algorithm>
#include <any>
#include <functional>
#include <iostream>
#include <memory>
#include <prop_erasure.h>
#include <stdexcept>
#include <string>
#include <variant>

unsigned int PropErasure::with_proof_arg(const unsigned int n) { return n; }

unsigned int PropErasure::add_with_proof(const unsigned int _x0,
                                         const unsigned int _x1) {
  return (_x0 + _x1);
}
