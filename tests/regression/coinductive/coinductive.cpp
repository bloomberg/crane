#include "coinductive.h"

Coinductive::stream Coinductive::zeros() {
  return stream::lazy_([]() -> typename Coinductive::stream::Cons {
    return {UINT64_C(0), zeros()};
  });
}

Coinductive::stream Coinductive::count_from(uint64_t n) {
  return stream::lazy_([=]() -> typename Coinductive::stream::Cons {
    return {n, count_from((n + 1))};
  });
}

uint64_t Coinductive::hd(const Coinductive::stream &s) {
  const auto &[a0, a1] = std::get<typename Coinductive::stream::Cons>(s.v());
  return a0;
}

Coinductive::stream Coinductive::tl(const Coinductive::stream &s) {
  const auto &[a0, a1] = std::get<typename Coinductive::stream::Cons>(s.v());
  return a1;
}

Coinductive::stream Coinductive::interleave(const Coinductive::stream &s1,
                                            const Coinductive::stream &s2) {
  const auto &[a0, a1] = std::get<typename Coinductive::stream::Cons>(s1.v());
  return stream::lazy_([=]() -> typename Coinductive::stream::Cons {
    return {a0, interleave(s2, a1)};
  });
}

Coinductive::tree Coinductive::infinite_tree(uint64_t n) {
  return tree::lazy_([=]() -> typename Coinductive::tree::Node {
    return {n, infinite_tree((n + UINT64_C(1))),
            infinite_tree((n + UINT64_C(2)))};
  });
}
