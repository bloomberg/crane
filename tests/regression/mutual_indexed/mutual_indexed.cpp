#include "mutual_indexed.h"

unsigned int MutualIndexed::even_val(unsigned int,
                                     const MutualIndexed::EvenTree &t) {
  if (std::holds_alternative<typename MutualIndexed::EvenTree::ELeaf>(t.v())) {
    return 0u;
  } else {
    const auto &[n, a1, a2] =
        std::get<typename MutualIndexed::EvenTree::ENode>(t.v());
    return a1;
  }
}

unsigned int MutualIndexed::odd_val(unsigned int,
                                    const MutualIndexed::OddTree &t) {
  const auto &[n, a1, a2] =
      std::get<typename MutualIndexed::OddTree::ONode>(t.v());
  return a1;
}
