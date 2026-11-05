#include <lifted_helper_frame_pointer.h>

#include <cstdint>
#include <cstdlib>
#include <iostream>

using L = LiftedHelperFramePointer;

static int failures = 0;

static void expect(const char *what, uint64_t got, uint64_t want) {
  if (got != want) {
    std::cerr << what << ": got " << got << ", want " << want << "\n";
    ++failures;
  }
}

int main() {
  // zigzag t u s w = go t u + 1000 * go s w; go_ref is the same recursion
  // left at the top level.
  for (uint64_t n = 0; n <= 6; ++n) {
    for (uint64_t m = 0; m <= 3; ++m) {
      auto t = L::full(n);
      auto u = L::full(m);
      auto s = L::full_bool(m);
      auto w = L::full_bool(n);
      expect("zigzag full", L::zigzag(t, u, s, w), L::go_ref(t, u) + 1000 * L::go_ref(s, w));
    }
  }
  // The helper's machine keeps its frames on the heap: a spine far deeper
  // than the C++ stack.
  auto deep = L::spine(200000);
  auto leaf = L::spine(0);
  expect("zigzag deep", L::zigzag(deep, leaf, L::full_bool(0), L::full_bool(1)),
         L::go_ref(deep, leaf) + 1000 * L::go_ref(L::full_bool(0), L::full_bool(1)));
  // A spine's leaves: the first is beside the tree passed (a node: 1), every
  // later one beside the leaf left of its parent (0).
  expect("go_ref spine", L::go_ref(L::spine(3), L::spine(1)), 1);
  expect("zigzag spine", L::zigzag(L::spine(3), L::spine(1), L::full_bool(2), L::full_bool(1)),
         1 + 1000 * L::go_ref(L::full_bool(2), L::full_bool(1)));
  return failures == 0 ? EXIT_SUCCESS : EXIT_FAILURE;
}
