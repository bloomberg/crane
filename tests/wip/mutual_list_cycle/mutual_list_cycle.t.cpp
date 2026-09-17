#include <mutual_list_cycle.h>

#include <cassert>

namespace {

int to_int(const Nat &n) {
  int acc = 0;
  const Nat *cur = &n;
  while (std::holds_alternative<Nat::S>(cur->v())) {
    ++acc;
    cur = std::get<Nat::S>(cur->v()).a0.get();
  }
  return acc;
}

} // namespace

int main() {
  Tree leaf = Tree::leaf(List<Branch>::nil());
  assert(to_int(leaf.tree_size()) == 1);

  Branch b = Branch::branch0(Nat::o(), leaf);
  assert(to_int(b.branch_size()) == 2);

  Tree node = Tree::leaf(List<Branch>::cons(b, List<Branch>::nil()));
  assert(to_int(node.tree_size()) == 3);

  return 0;
}
