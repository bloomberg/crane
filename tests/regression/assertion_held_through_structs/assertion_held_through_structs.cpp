#include "assertion_held_through_structs.h"

uint64_t AssertionHeldThroughStructs::Mid::S::lookup(uint64_t k) {
  return (k + UINT64_C(1));
}

uint64_t AssertionHeldThroughStructs::Mid::Inner::S2::lookup(uint64_t k) {
  return (k + UINT64_C(2));
}
