#include <mutual_indexed.h>

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

__attribute__((pure)) unsigned int
MutualIndexed::even_val(const unsigned int,
                        const std::shared_ptr<MutualIndexed::EvenTree> &t) {
  if (std::holds_alternative<typename MutualIndexed::EvenTree::ELeaf>(t->v())) {
    return 0u;
  } else {
    const auto &_m =
        *std::get_if<typename MutualIndexed::EvenTree::ENode>(&t->v());
    return _m.d_a1;
  }
}

__attribute__((pure)) unsigned int
MutualIndexed::odd_val(const unsigned int,
                       const std::shared_ptr<MutualIndexed::OddTree> &t) {
  const auto &_m =
      *std::get_if<typename MutualIndexed::OddTree::ONode>(&t->v());
  return _m.d_a1;
}
