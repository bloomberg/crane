#include "loopify_cont_box_pointer.h"

LoopifyContBoxPointer::tree LoopifyContBoxPointer::build(uint64_t n) {
  return ListDef::seq(UINT64_C(0), n)
      .template fold_left<LoopifyContBoxPointer::tree>(
          [](const LoopifyContBoxPointer::tree &t, uint64_t k) {
            return t.insert(k);
          },
          tree::leaf());
}

LoopifyContBoxPointer::reader
LoopifyContBoxPointer::read_with(LoopifyContBoxPointer::tree t) {
  return reader::reader0(
      [=, t = std::move(t)](uint64_t x) { return (x + t.sum()); });
}

List<uint64_t> ListDef::seq(uint64_t start, uint64_t len) {
  if (len <= 0) {
    return List<uint64_t>::nil();
  } else {
    uint64_t len0 = len - 1;
    return List<uint64_t>::cons(start, ListDef::seq((start + 1), len0));
  }
}
