#include "coinductive.h"

Coinductive::stream Coinductive::zeros() {
  return stream::lazy_([]() -> Coinductive::stream {
    return stream::cons(UINT64_C(0), zeros());
  });
}

Coinductive::stream Coinductive::count_from(uint64_t n) {
  return stream::lazy_([=]() mutable -> Coinductive::stream {
    return stream::cons(n, count_from((n + 1)));
  });
}

uint64_t Coinductive::hd(Coinductive::stream s) {
  const auto &[a0, a1] = std::get<typename Coinductive::stream::Cons>(s.v());
  return a0;
}

Coinductive::stream Coinductive::tl(Coinductive::stream s) {
  const auto &[a0, a1] = std::get<typename Coinductive::stream::Cons>(s.v());
  return stream::lazy_([=]() mutable -> Coinductive::stream { return *a1; });
}

Coinductive::stream Coinductive::interleave(Coinductive::stream s1,
                                            Coinductive::stream s2) {
  const auto &[a0, a1] = std::get<typename Coinductive::stream::Cons>(s1.v());
  return stream::lazy_([=]() mutable -> Coinductive::stream {
    return stream::cons(a0, interleave(s2, *a1));
  });
}

Coinductive::tree Coinductive::infinite_tree(uint64_t n) {
  return tree::lazy_([=]() mutable -> Coinductive::tree {
    return tree::node(n, infinite_tree((n + UINT64_C(1))),
                      infinite_tree((n + UINT64_C(2))));
  });
}
