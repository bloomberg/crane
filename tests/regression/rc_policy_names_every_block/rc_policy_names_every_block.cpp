#include "rc_policy_names_every_block.h"

RcPolicyNamesEveryBlock::stream RcPolicyNamesEveryBlock::from(uint64_t n) {
  return stream::lazy_([=]() -> RcPolicyNamesEveryBlock::stream {
    return stream::scons(n, from((n + 1)));
  });
}

uint64_t RcPolicyNamesEveryBlock::hd(const RcPolicyNamesEveryBlock::stream &s) {
  const auto &[a0, a1] =
      std::get<typename RcPolicyNamesEveryBlock::stream::SCons>(s.v());
  return a0;
}
