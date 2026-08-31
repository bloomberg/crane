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
  // Sanity: shallow trees round-trip fine.  The depth is capped at 5k because
  // `tsum` recurses through an inner `fix` over `lst tree` that loopify does
  // not flatten, so the traversal -- unlike the destruction below -- still
  // costs a stack frame per level.  That is a separate limitation from the
  // drain this test covers.
  for (unsigned n : {1000u, 5000u}) {
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
  // Depth is capped at 200k because `spine` itself is *not* loopified -- it is
  // a methodified tail call whose receiver is a fresh value, which loopify
  // declines ("value-type receiver, whose address cannot be stored in a
  // frame").  Building deeper overflows in construction, which is a separate
  // limitation from the drain this test covers.
  for (unsigned n : {200000u}) {
    {
      auto *p = new tree(build(n));
      std::cout << n << ": built" << std::flush;
      delete p; // <-- stack overflow here
    }
    std::cout << " destroyed" << std::endl;
  }
  return 0;
}
