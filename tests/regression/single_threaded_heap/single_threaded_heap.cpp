#include "single_threaded_heap.h"

SingleThreadedHeap::tree
SingleThreadedHeap::insert(uint64_t k, const SingleThreadedHeap::tree &t) {
  if (crane::holds_alternative<typename SingleThreadedHeap::tree::Leaf>(
          t.v())) {
    return tree::node(tree::leaf(), k, tree::leaf());
  } else {
    const auto &[a0, a1, a2] =
        crane::get<typename SingleThreadedHeap::tree::Node>(t.v());
    if (k < a1) {
      return tree::node(insert(k, *a0), a1, *a2);
    } else {
      return tree::node(*a0, a1, insert(k, *a2));
    }
  }
}

uint64_t SingleThreadedHeap::size(const SingleThreadedHeap::tree &t) {
  if (crane::holds_alternative<typename SingleThreadedHeap::tree::Leaf>(
          t.v())) {
    return UINT64_C(0);
  } else {
    const auto &[a0, a1, a2] =
        crane::get<typename SingleThreadedHeap::tree::Node>(t.v());
    return ((UINT64_C(1) + size(*a0)) + size(*a2));
  }
}

uint64_t SingleThreadedHeap::adder(uint64_t x0_, uint64_t x1_) {
  return (x0_ + x1_);
}

List<uint64_t> ListDef::seq(uint64_t start, uint64_t len) {
  if (len <= 0) {
    return List<uint64_t>::nil();
  } else {
    uint64_t len0 = len - 1;
    return List<uint64_t>::cons(start, ListDef::seq((start + 1), len0));
  }
}
