#include <coinductive.h>

__attribute__((pure)) Coinductive::stream Coinductive::zeros() {
  return stream::lazy_(
      []() -> Coinductive::stream { return stream::cons(0u, zeros()); });
}

__attribute__((pure)) Coinductive::stream
Coinductive::count_from(unsigned int n) {
  return stream::lazy_([=]() mutable -> Coinductive::stream {
    return stream::cons(n, count_from((n + 1)));
  });
}

__attribute__((pure)) unsigned int
Coinductive::hd(const Coinductive::stream s) {
  const auto &[d_a0, d_a1] =
      std::get<typename Coinductive::stream::Cons>(s.v());
  return d_a0;
}

__attribute__((pure)) Coinductive::stream
Coinductive::tl(const Coinductive::stream s) {
  const auto &[d_a0, d_a1] =
      std::get<typename Coinductive::stream::Cons>(s.v());
  return stream::lazy_(
      [=]() mutable -> Coinductive::stream { return *(d_a1); });
}

__attribute__((pure)) Coinductive::stream
Coinductive::interleave(const Coinductive::stream s1,
                        const Coinductive::stream s2) {
  const auto &[d_a0, d_a1] =
      std::get<typename Coinductive::stream::Cons>(s1.v());
  return stream::lazy_([=]() mutable -> Coinductive::stream {
    return stream::cons(d_a0, interleave(s2, *(d_a1)));
  });
}

__attribute__((pure)) Coinductive::tree
Coinductive::infinite_tree(unsigned int n) {
  return tree::lazy_([=]() mutable -> Coinductive::tree {
    return tree::node(n, infinite_tree((n + 1u)), infinite_tree((n + 2u)));
  });
}
