#include "nested_tree_pair_literal.h"

/// A non-uniform (nested) inductive
/// (tree A := Lf : A -> tree A | Nd : tree (A * A) -> tree A) has its type
/// parameter erased, so a literal value built at tree nat passes a
/// std::pair through the erased constructor.
uint64_t NestedTreePairLiteral::size(const NestedTreePairLiteral::tree &t) {
  if (std::holds_alternative<typename NestedTreePairLiteral::tree::Lf>(t.v())) {
    return UINT64_C(1);
  } else {
    const auto &[a0] =
        std::get<typename NestedTreePairLiteral::tree::Nd>(t.v());
    return UINT64_C(2) * size(*a0);
  }
}
