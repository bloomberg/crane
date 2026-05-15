#include "pair_self_deep_copy.h"

std::pair<PairSelfDeepCopy::chain, PairSelfDeepCopy::chain>
PairSelfDeepCopy::dup_chain(PairSelfDeepCopy::chain c) {
  return std::make_pair(std::move(c), c);
}
