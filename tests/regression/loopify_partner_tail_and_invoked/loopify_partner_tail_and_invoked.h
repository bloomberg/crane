#ifndef INCLUDED_LOOPIFY_PARTNER_TAIL_AND_INVOKED
#define INCLUDED_LOOPIFY_PARTNER_TAIL_AND_INVOKED

#include "small_vector.h"
#include <atomic>
#include <cstdint>
#include <utility>
#include <variant>

/// walk calls its partner step both as a tail call and as the operand
/// of an addition, and step calls walk back where its body runs.  Its
/// machine continues in step's body at the tail call and enters a copy of
/// step at the other, whose calls of walk are turns of the one machine:
/// no call between the two runs on the C++ stack, however deep.
struct LoopifyPartnerTailAndInvoked {
  static uint64_t walk(uint64_t n);
  static uint64_t step(uint64_t n);
};

#endif // INCLUDED_LOOPIFY_PARTNER_TAIL_AND_INVOKED
