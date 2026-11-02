#include <loopify_mutual_result_types.h>
#include <iostream>
using M = LoopifyMutualResultTypes;

// A value alternating e and md 100000 deep: every level passes a call of the
// partner that a copy spliced into sum_e brought, which sum_e's machine has to
// enter rather than make on the C++ stack.
static bool deep_alternation() {
  M::e cur = M::e::leaf(1);
  for (int i = 0; i < 100000; ++i)
    cur = M::e::meta(M::md::mpair(M::md::mconst(M::e::add(std::move(cur), M::e::leaf(0))), M::md::mnull()));
  return M::sum_e(cur) == 1;
}

int main() {
  bool ok = M::check(std::monostate{}) && deep_alternation();
  std::cout << (ok ? "ok" : "wrong") << std::endl;
  return ok ? 0 : 1;
}
