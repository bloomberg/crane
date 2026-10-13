#include "alias_mapped_inductive_match.h"

uint64_t AliasMappedInductiveMatch::get(const std::optional<uint64_t> &o) {
  if (std::holds_alternative<
          typename AliasMappedInductiveMatch::std::optional<uint64_t>::No>(
          o.v())) {
    return UINT64_C(0);
  } else {
    const auto &[a0] = std::get<
        typename AliasMappedInductiveMatch::std::optional<uint64_t>::Yes>(
        o.v());
    return a0;
  }
}
