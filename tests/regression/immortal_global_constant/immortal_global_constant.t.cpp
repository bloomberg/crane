// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <immortal_global_constant.h>
#include <cassert>
#include <cstddef>
#include <conslist.h>
#include <shared_array.h>

using M = ImmortalGlobalConstant;
using Tree = M::tree;

static constexpr std::size_t immortal = ~std::size_t{0};

// Every block of [t] is immortal.
static bool all_immortal(const Tree &t) {
  auto *n = crane::get_if<Tree::Node>(&t.v());
  if (!n) return true;
  return t.v().use_count() == immortal && all_immortal(*n->a0) && all_immortal(*n->a2);
}

int main() {
  // A global, and what a pair, a list and a record of the globals hold.
  assert(crane::get_if<Tree::Node>(&M::table.v()) && all_immortal(M::table));
  assert(all_immortal(M::pair_table.first));
  for (const List<Tree> *l = &M::pair_table.second; auto *c = crane::get_if<List<Tree>::Cons>(&l->v()); l = &*c->l)
    assert(l->v().use_count() == immortal && all_immortal(c->a));
  assert(all_immortal(M::entry_table.value));
  // The long list: its last cell was queued, not reached by recursion.
  {
    const List<uint64_t> *l = &M::long_table;
    std::size_t n = 0;
    while (auto *c = crane::get_if<List<uint64_t>::Cons>(&l->v())) {
      assert(l->v().use_count() == immortal);
      ++n;
      l = &*c->l;
    }
    assert(n == 100000);
  }
  // Copies and drops of a constant leave its counts alone.
  {
    Tree copy = M::table;
    assert(M::table.v().use_count() == immortal);
    assert(M::sizes(1000) == 1000 * 15);
    assert(M::table.v().use_count() == immortal);
  }
  // A value built at run time is counted, and its copies too.
  {
    Tree t = M::fresh(3);
    assert(t.v().use_count() == 1);
    Tree u = t;
    assert(t.v().use_count() == 2);
  }
  // The runtime's own containers: a cons list's cells and an array's block,
  // and what they hold.
  {
    auto l = crane::list<Tree>::cons(M::fresh(2), crane::list<Tree>::cons(M::fresh(1), {}));
    crane::make_immortal(l);
    for (const Tree &t : l) assert(all_immortal(t));
    auto a = crane::shared_array<Tree>::of_range(l);
    crane::make_immortal(a);
    assert(all_immortal(a[0]) && all_immortal(a[1]));
    auto b = a;
    auto m = l;
  }
  return 0;
}
