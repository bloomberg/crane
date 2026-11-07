// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
// A unit with both the scoped arena and non-atomic reference counts: trees
// built inside and outside an arena scope through crane::rc<T>::make.
#include <arena_non_atomic_rc.h>

#include <iostream>
#include <variant>

namespace {
int testStatus = 0;
void aSsErT(bool condition, const char *message, int line) {
  if (condition) {
    std::cout << "Error " __FILE__ "(" << line << "): " << message
              << "    (failed)" << std::endl;
    if (0 <= testStatus && testStatus <= 100) ++testStatus;
  }
}
} // namespace
#define ASSERT(X) aSsErT(!(X), #X, __LINE__);

namespace {
using T = ArenaNonAtomicRc::tree;

Nat nat(unsigned n) {
  Nat r = Nat::o();
  for (unsigned i = 0; i < n; ++i) r = Nat::s(r);
  return r;
}

unsigned value(const Nat &n) {
  unsigned k = 0;
  const Nat *p = &n;
  while (std::holds_alternative<Nat::S>(p->v())) {
    p = &*std::get<Nat::S>(p->v()).a0;
    ++k;
  }
  return k;
}

T build(int d) {
  if (d == 0) return T::leaf();
  return T::node(build(d - 1), nat(d), build(d - 1));
}

unsigned root(const T &t) { return value(std::get<T::Node>(t.v()).a1); }
} // namespace

int main() {
  // Outside every arena scope the factory allocates on the heap.
  ASSERT(value(ArenaNonAtomicRc::size(build(3))) == 15);
  {
    crane::arena_scope s;
    T t = build(8);
    ASSERT(value(ArenaNonAtomicRc::size(t)) == 511);
    T u = T::node(T::node(T::leaf(), nat(1), T::leaf()), nat(2),
                  T::node(T::leaf(), nat(3), T::leaf()));
    T m = ArenaNonAtomicRc::mirror(u);
    ASSERT(root(m) == 2);
    ASSERT(root(*std::get<T::Node>(m.v()).a0) == 3);
    ASSERT(root(*std::get<T::Node>(m.v()).a2) == 1);
  }
  if (testStatus > 0)
    std::cerr << "arena_non_atomic_rc: " << testStatus << " test(s) FAILED\n";
  return testStatus;
}
