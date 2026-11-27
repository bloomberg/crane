#include "shared_child_cells.h"

SharedChildCells::tree
SharedChildCells::insert(uint64_t x, const SharedChildCells::tree &t) {
  if (std::holds_alternative<typename SharedChildCells::tree::Leaf>(t.v())) {
    return tree::node(tree::leaf(), x, tree::leaf());
  } else {
    const auto &[l0, k0, r0] =
        std::get<typename SharedChildCells::tree::Node>(t.v());
    if (x < k0) {
      return tree::node(insert(x, *l0), k0, crane::shared_child(r0));
    } else if (k0 < x) {
      return tree::node(crane::shared_child(l0), k0, insert(x, *r0));
    } else {
      return t;
    }
  }
}

uint64_t SharedChildCells::sum(const SharedChildCells::tree &t) {
  if (std::holds_alternative<typename SharedChildCells::tree::Leaf>(t.v())) {
    return UINT64_C(0);
  } else {
    const auto &[l0, k0, r0] =
        std::get<typename SharedChildCells::tree::Node>(t.v());
    return sum(*l0) + k0 + sum(*r0);
  }
}

/// Swaps the children: both are fields read out of the matched value.
SharedChildCells::tree
SharedChildCells::mirror_root(const SharedChildCells::tree &t) {
  if (std::holds_alternative<typename SharedChildCells::tree::Leaf>(t.v())) {
    return tree::leaf();
  } else {
    const auto &[l0, k0, r0] =
        std::get<typename SharedChildCells::tree::Node>(t.v());
    return tree::node(crane::shared_child(r0), k0, crane::shared_child(l0));
  }
}
