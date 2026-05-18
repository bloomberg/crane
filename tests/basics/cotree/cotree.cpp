#include "cotree.h"

Cotree::colist<uint64_t> Cotree::nats(uint64_t n) {
  return colist<uint64_t>::lazy_([=]() mutable -> Cotree::colist<uint64_t> {
    return colist<uint64_t>::cocons(n, nats((n + 1)));
  });
}

Cotree::colist<uint64_t> Cotree::binary_children(uint64_t n) {
  return colist<uint64_t>::lazy_([=]() mutable -> Cotree::colist<uint64_t> {
    return colist<uint64_t>::cocons(
        ((UINT64_C(2) * n) + UINT64_C(1)),
        colist<uint64_t>::cocons(((UINT64_C(2) * n) + UINT64_C(2)),
                                 colist<uint64_t>::conil()));
  });
}
