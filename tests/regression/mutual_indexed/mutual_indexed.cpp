#include <mutual_indexed.h>

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

__attribute__((pure)) unsigned int
MutualIndexed::even_val(const unsigned int &,
                        const MutualIndexed::EvenTree &t) {
  if (std::holds_alternative<typename MutualIndexed::EvenTree::ELeaf>(t.v())) {
    return 0u;
  } else {
    const auto &[d_n, d_a1, d_a2] =
        std::get<typename MutualIndexed::EvenTree::ENode>(t.v());
    return d_a1;
  }
}

__attribute__((pure)) unsigned int
MutualIndexed::odd_val(const unsigned int &, const MutualIndexed::OddTree &t) {
  const auto &[d_n, d_a1, d_a2] =
      std::get<typename MutualIndexed::OddTree::ONode>(t.v());
  return d_a1;
}
