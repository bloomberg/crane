#include <loopify_out_of_line_method.h>

#include <cassert>
#include <cstdint>
#include <cstdlib>

int main() {
  assert(Tree::leaf().depth() == 0);
  assert(Tree::node(Forest::bare(), Tree::leaf()).depth() == 1);

  // A million nodes deep: a method recursing in C++ overflows the stack.
  constexpr uint64_t n = 1000000;
  Tree t = Tree::leaf();
  for (uint64_t i = 0; i < n; ++i) {
    t = Tree::node(Forest::bare(), std::move(t));
  }
  assert(t.depth() == n);

  // Releasing the chain is not what this test is about.
  std::_Exit(0);
}
