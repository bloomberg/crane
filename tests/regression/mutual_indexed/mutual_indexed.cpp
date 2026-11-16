#include "mutual_indexed.h"

uint64_t MutualIndexed::even_val(uint64_t, const MutualIndexed::EvenTree &t) {
  if (std::holds_alternative<typename MutualIndexed::EvenTree::ELeaf>(t.v())) {
    return UINT64_C(0);
  } else {
    const auto &[_, a1, _] =
        std::get<typename MutualIndexed::EvenTree::ENode>(t.v());
    return a1;
  }
}

uint64_t MutualIndexed::odd_val(uint64_t, const MutualIndexed::OddTree &t) {
  const auto &[_, a1, _] =
      std::get<typename MutualIndexed::OddTree::ONode>(t.v());
  return a1;
}
