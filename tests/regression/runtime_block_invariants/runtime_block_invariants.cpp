#include "runtime_block_invariants.h"

RuntimeBlockInvariants::stream RuntimeBlockInvariants::from(uint64_t n) {
  return stream::lazy_([=]() -> typename RuntimeBlockInvariants::stream::SCons {
    return {n, from((n + 1))};
  });
}

uint64_t RuntimeBlockInvariants::hd(const RuntimeBlockInvariants::stream &s) {
  const auto &[a0, a1] =
      std::get<typename RuntimeBlockInvariants::stream::SCons>(s.v());
  return a0;
}
