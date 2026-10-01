#include <point_free_fix_binder_untyped.h>

#include <any>
#include <cassert>
#include <cstdio>

/// [tree]'s payload is [Params]' [base], so [Tree] is parameterised by it;
/// [nat_params] is the instance [go] runs at.
using Tr = Tree<typename nat_params::base>;

/// The number of [Leaf]s in [t].  [Tree] is a variant, so the shape has to be
/// walked rather than asked for.
static int leaves(const Tr &t) {
  if (std::holds_alternative<typename Tr::Leaf>(t.v())) {
    return 1;
  }
  int n = 0;
  const List<Tr> *cur = std::get<typename Tr::Node>(t.v()).kids.get();
  while (std::holds_alternative<typename List<Tr>::Cons>(cur->v())) {
    const auto &cell = std::get<typename List<Tr>::Cons>(cur->v());
    n += leaves(cell.a);
    cur = cell.l.get();
  }
  return n;
}

int main() {
  // The defect this test pins was a compile failure: the lambda
  // [general_optimize_fix] wraps around the point-free occurrence of [freeze]
  // had its binder typed [Taxiom], which printed as the undeclared C++ type
  // [axiom].  Reaching main at all is most of the assertion.  The rest checks
  // that the recursion still traverses, so that a binder typed into silence
  // would not pass.
  const Tr leaf = Tr::leaf(Nat::o());
  const Tr node = Tr::node(
      List<Tr>::cons(leaf, List<Tr>::cons(leaf, List<Tr>::nil())));

  const std::optional<Tr> flat = go(leaf);
  assert(flat.has_value());
  assert(leaves(*flat) == 1);

  const std::optional<Tr> deep = go(node);
  assert(deep.has_value());
  assert(leaves(*deep) == 2);

  std::printf("ok\n");
  return 0;
}
