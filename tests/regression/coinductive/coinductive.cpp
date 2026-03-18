#include <coinductive.h>

#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

std::shared_ptr<Coinductive::stream> Coinductive::zeros() {
  return stream::ctor::lazy_([](void) -> std::shared_ptr<Coinductive::stream> {
    return stream::ctor::Cons_(0u, zeros());
  });
}

std::shared_ptr<Coinductive::stream>
Coinductive::count_from(const unsigned int n) {
  return stream::ctor::lazy_(
      [=](void) mutable -> std::shared_ptr<Coinductive::stream> {
        return stream::ctor::Cons_(n, count_from((n + 1)));
      });
}

__attribute__((pure)) unsigned int
Coinductive::hd(const std::shared_ptr<Coinductive::stream> &s) {
  return std::visit(
      Overloaded{[](const typename Coinductive::stream::Cons _args)
                     -> unsigned int { return _args.d_a0; }},
      s->v());
}

std::shared_ptr<Coinductive::stream>
Coinductive::tl(const std::shared_ptr<Coinductive::stream> &s) {
  return stream::ctor::lazy_(
      [=](void) mutable -> std::shared_ptr<Coinductive::stream> {
        return std::visit(
            Overloaded{[](const typename Coinductive::stream::Cons _args)
                           -> std::shared_ptr<Coinductive::stream> {
              return _args.d_a1;
            }},
            s->v());
      });
}

std::shared_ptr<Coinductive::stream>
Coinductive::interleave(const std::shared_ptr<Coinductive::stream> &s1,
                        std::shared_ptr<Coinductive::stream> s2) {
  return stream::ctor::lazy_(
      [=](void) mutable -> std::shared_ptr<Coinductive::stream> {
        return std::visit(
            Overloaded{[&](const typename Coinductive::stream::Cons _args)
                           -> std::shared_ptr<Coinductive::stream> {
              return stream::ctor::Cons_(_args.d_a0,
                                         interleave(s2, _args.d_a1));
            }},
            s1->v());
      });
}

std::shared_ptr<Coinductive::tree>
Coinductive::infinite_tree(const unsigned int n) {
  return tree::ctor::lazy_(
      [=](void) mutable -> std::shared_ptr<Coinductive::tree> {
        return tree::ctor::Node_(n, infinite_tree((n + 1u)),
                                 infinite_tree((n + 2u)));
      });
}
