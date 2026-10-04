// A mutual group of free template functions under separate extraction
// (tmap/fmap in Tr.v, over types from Ty.v): tmap calls fmap<T1, T2> before
// fmap is defined, which compiles only because Tr.h declares the whole group
// first.
#include "Ty.h"
#include "Tr.h"
#include "SepExtMutualTemplateOrder.h"

#include <cassert>

int main() {
  using Tree = Ty::Tree<bool>;
  using Forest = Ty::Forest<bool>;
  Tree leaf = Tree::node(false, Forest::nil());
  Tree t = Tree::node(true, Forest::cons(leaf, Forest::nil()));
  Tree u = SepExtMutualTemplateOrder::use_it(t);
  const auto &[a, fs] = std::get<Tree::Node>(u.v());
  assert(!a);
  const auto &[child, rest] = std::get<Forest::Cons>(fs->v());
  assert(std::get<Tree::Node>(child->v()).a0);
  return 0;
}
