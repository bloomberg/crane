// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <product_conversion.h>

#include <any>
#include <cassert>
#include <cstdint>
#include <iostream>
#include <type_traits>

using P = ProductConversion;
struct Unrelated {};

// No route for one field: no conversion at all, rather than one that throws.
static_assert(!std::is_convertible_v<P::pair<int, int>, P::pair<Unrelated, int>>);
static_assert(!std::is_convertible_v<P::pair<int, int>, P::pair<int, Unrelated>>);
static_assert(!std::is_convertible_v<P::tagged<int>, P::tagged<Unrelated>>);
// A route for every field: the conversion is there.
static_assert(std::is_convertible_v<P::pair<int, int>, P::pair<std::any, int>>);
static_assert(std::is_convertible_v<P::tagged<int>, P::tagged<std::any>>);

int main() {
  P::pair<int, uint64_t> p = P::pair<int, uint64_t>::mk(1, 2);
  P::pair<std::any, uint64_t> q = p;
  assert(std::any_cast<int>(q.a) == 1 && q.b == 2);
  P::tagged<std::any> t = P::tagged<int>{UINT64_C(7), 8};
  assert(t.tag == 7 && std::any_cast<int>(t.payload) == 8);
  // A million cells read at another element type, at -O0: the recursive
  // conversion would take a native frame per cell.
  P::list<int> l = P::list<int>::nil();
  for (int i = 1000000; i > 0; --i) {
    l = P::list<int>::cons(i, std::move(l));
  }
  P::list<std::any> m = l;
  const P::list<std::any> *c = &m;
  long n = 0;
  int last = 0;
  while (std::holds_alternative<P::list<std::any>::Cons>(c->v())) {
    const auto &cell = std::get<P::list<std::any>::Cons>(c->v());
    last = std::any_cast<int>(cell.a);
    ++n;
    c = cell.l.get();
  }
  assert(n == 1000000 && last == 1000000);
  std::cout << "product_conversion: ok\n";
  return 0;
}
