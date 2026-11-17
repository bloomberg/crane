#include "ptr_word.h"

uint64_t PtrWord::size(const PtrWord::tree &t) {
  if (crane::holds_alternative<typename PtrWord::tree::Leaf>(t.v())) {
    return UINT64_C(1);
  } else {
    const auto &[l0, r0] = crane::get<typename PtrWord::tree::Node>(t.v());
    return (size(*l0) + size(*r0));
  }
}
