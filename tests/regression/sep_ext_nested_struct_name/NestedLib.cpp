#include "NestedLib.h"

namespace NestedLib {

uint64_t Sub::size(const Sub::Tree &t) {
  if (std::holds_alternative<typename Sub::Tree::Leaf>(t.v())) {
    return UINT64_C(0);
  } else {
    const auto &[a0, a1, a2] = std::get<typename Sub::Tree::Node>(t.v());
    return ((size(*a0) + size(*a2)) + 1);
  }
}

} // namespace NestedLib
