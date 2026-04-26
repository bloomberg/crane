#include <coinductive.h>

#include <functional>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

std::shared_ptr<Coinductive::stream> Coinductive::zeros() {
  return stream::lazy_([]() -> std::shared_ptr<Coinductive::stream> {
    return stream::cons(0u, zeros());
  });
}

std::shared_ptr<Coinductive::stream> Coinductive::count_from(unsigned int n) {
  return stream::lazy_([=]() mutable -> std::shared_ptr<Coinductive::stream> {
    return stream::cons(n, count_from((n + 1)));
  });
}

__attribute__((pure)) unsigned int
Coinductive::hd(const std::shared_ptr<Coinductive::stream> &s) {
  const auto &[d_a0, d_a1] =
      std::get<typename Coinductive::stream::Cons>(s->v());
  return d_a0;
}

std::shared_ptr<Coinductive::stream>
Coinductive::tl(const std::shared_ptr<Coinductive::stream> &s) {
  const auto &[d_a0, d_a1] =
      std::get<typename Coinductive::stream::Cons>(s->v());
  return stream::lazy_(
      [=]() mutable -> std::shared_ptr<Coinductive::stream> { return d_a1; });
}

std::shared_ptr<Coinductive::stream>
Coinductive::interleave(const std::shared_ptr<Coinductive::stream> &s1,
                        const std::shared_ptr<Coinductive::stream> &s2) {
  const auto &[d_a0, d_a1] =
      std::get<typename Coinductive::stream::Cons>(s1->v());
  return stream::lazy_([=]() mutable -> std::shared_ptr<Coinductive::stream> {
    return stream::cons(d_a0, interleave(s2, d_a1));
  });
}

std::shared_ptr<Coinductive::tree> Coinductive::infinite_tree(unsigned int n) {
  return tree::lazy_([=]() mutable -> std::shared_ptr<Coinductive::tree> {
    return tree::node(n, infinite_tree((n + 1u)), infinite_tree((n + 2u)));
  });
}
