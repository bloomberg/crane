#include "optional_self_deep_copy.h"

std::pair<OptionalSelfDeepCopy::chain, OptionalSelfDeepCopy::chain>
OptionalSelfDeepCopy::dup_chain(OptionalSelfDeepCopy::chain c) {
  return std::make_pair(c, c);
}
