#include <coinductive.h>

#include <functional>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

std::shared_ptr<Coinductive::stream> Coinductive::zeros() {
  return stream::lazy_([]() -> std::shared_ptr<Coinductive::stream> {
    return stream::cons(0u, zeros());
  });
}

std::shared_ptr<Coinductive::stream>
Coinductive::count_from(const unsigned int n) {
  return stream::lazy_([=]() mutable -> std::shared_ptr<Coinductive::stream> {
    return stream::cons(n, count_from((n + 1)));
  });
}

__attribute__((pure)) unsigned int
Coinductive::hd(const std::shared_ptr<Coinductive::stream> &s) {
  return std::visit(
      Overloaded{[](const typename Coinductive::stream::Cons &_args)
                     -> unsigned int { return _args.d_a0; }},
      s->v());
}

std::shared_ptr<Coinductive::stream>
Coinductive::tl(const std::shared_ptr<Coinductive::stream> &s) {
  return stream::lazy_([=]() mutable -> std::shared_ptr<Coinductive::stream> {
    return std::visit(
        Overloaded{
            [](const typename Coinductive::stream::Cons &_args)
                -> std::shared_ptr<Coinductive::stream> { return _args.d_a1; }},
        s->v());
  });
}

std::shared_ptr<Coinductive::stream>
Coinductive::interleave(const std::shared_ptr<Coinductive::stream> &s1,
                        const std::shared_ptr<Coinductive::stream> &s2) {
  return stream::lazy_([=]() mutable -> std::shared_ptr<Coinductive::stream> {
    return std::visit(
        Overloaded{[&](const typename Coinductive::stream::Cons &_args)
                       -> std::shared_ptr<Coinductive::stream> {
          return stream::cons(_args.d_a0, interleave(s2, _args.d_a1));
        }},
        s1->v());
  });
}

std::shared_ptr<Coinductive::tree>
Coinductive::infinite_tree(const unsigned int n) {
  return tree::lazy_([=]() mutable -> std::shared_ptr<Coinductive::tree> {
    return tree::node(n, infinite_tree((n + 1u)), infinite_tree((n + 2u)));
  });
}
