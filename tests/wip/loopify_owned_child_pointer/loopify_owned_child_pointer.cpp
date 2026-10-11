#include "loopify_owned_child_pointer.h"

LoopifyOwnedChildPointer::t LoopifyOwnedChildPointer::leaf(uint64_t n) {
  return t::n(n, std::make_pair(t::e(), t::e()));
}

LoopifyOwnedChildPointer::reader
LoopifyOwnedChildPointer::read_with(LoopifyOwnedChildPointer::t x) {
  return reader::reader0(
      [=, x = std::move(x)](uint64_t k) { return (k + x.sz()); });
}
