// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <shared_variant_constant.h>
#include <cassert>
#include <cstdint>

using M = SharedVariantConstant;

static std::uint64_t value(const Positive &p) {
  if (auto *x = crane::get_if<Positive::XI>(&p.v())) return 2 * value(*x->a0) + 1;
  if (auto *x = crane::get_if<Positive::XO>(&p.v())) return 2 * value(*x->a0);
  return 1;
}

int main() {
  // The same block every time, and it stays put: no count can free it.
  const void *a = crane::get_if<Positive::XI>(&M::seven(std::monostate{}).v());
  const void *b = crane::get_if<Positive::XI>(&M::seven(std::monostate{}).v());
  assert(a != nullptr && a == b);
  assert(value(M::seven(std::monostate{})) == 7);
  // 7 = xI (xI xH): the inner block is the constant's too, and immortal.
  const auto &inner = *crane::get_if<Positive::XI>(&M::seven(std::monostate{}).v())->a0;
  assert(inner.v().use_count() == ~std::size_t{0});
  auto p = M::pair_of(std::monostate{});
  assert(value(p.first) == 6 && value(p.second) == 12);
  assert(value(M::result) == 1 + 100 * 10);
  // 2^110 overflows the value check; its 110 xO nodes over xH are counted.
  {
    const Positive h = M::huge(std::monostate{});
    const Positive *p = &h;
    int zeros = 0;
    while (auto *x = crane::get_if<Positive::XO>(&p->v())) { ++zeros; p = &*x->a0; }
    assert(zeros == 110 && crane::holds_alternative<Positive::XH>(p->v()));
  }
  {
    auto r = M::with_k(List<Positive>::cons(M::seven(std::monostate{}), List<Positive>::nil()));
    auto length = [](const List<Positive> &l) {
      int n = 0;
      for (const List<Positive> *c = &l; auto *x = crane::get_if<List<Positive>::Cons>(&c->v()); c = &*x->l) ++n;
      return n;
    };
    assert(length(r.first) == 1 && length(r.second) == 2);
  }
  return 0;
}
