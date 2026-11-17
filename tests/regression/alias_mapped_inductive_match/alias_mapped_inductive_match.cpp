#include "alias_mapped_inductive_match.h"

uint64_t AliasMappedInductiveMatch::get(const std::optional<uint64_t> &o) {
  if (o.has_value()) {
    const uint64_t &n = *o;
    return n;
  } else {
    return UINT64_C(0);
  }
}
