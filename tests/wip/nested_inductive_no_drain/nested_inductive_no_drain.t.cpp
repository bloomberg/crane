#include <nested_inductive_no_drain.h>

#include <cassert>
#include <iostream>

namespace {
using tree = NestedInductiveNoDrain::tree;
template <typename A> using lst = NestedInductiveNoDrain::lst<A>;

tree build(unsigned n) {
  return tree::node(UINT64_C(0), lst<tree>::nil()).spine(n);
}
} // namespace

int main() {
  // Sanity: shallow trees round-trip fine.
  for (unsigned n : {1000u, 20000u}) {
    tree t = build(n);
    unsigned long long want = (unsigned long long)n * (n + 1) / 2;
    unsigned long long got = t.tsum();
    std::cout << n << ": sum=" << got << " (want " << want << ")" << std::endl;
    assert(got == want);
  }

  // The bug: build a deep tree and only *destroy* it -- no traversal at all.
  // `tree` recurses through `lst tree`, so Crane emits an iterative drain for
  // `~lst()` (walking the `a1` spine) but none for `tree`, and the drain never
  // descends into the `a0` element.  Destruction therefore recurses
  // ~lst<tree> -> ~tree -> ~lst<tree> -> ... once per level.
  for (unsigned n : {200000u, 2000000u}) {
    {
      auto *p = new tree(build(n));
      std::cout << n << ": built" << std::flush;
      delete p; // <-- stack overflow here
    }
    std::cout << " destroyed" << std::endl;
  }
  return 0;
}
