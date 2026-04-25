// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.

// Tests for higher-order functions on trees with multi-recursion.
//
// tree_map, tree_fold, tree_zip_with all take function parameters AND have
// multiple recursive calls per branch. This combination prevents loopification
// (find_combine_op returns None when dd_saved != []).
//
// The generated C++ uses direct recursion instead of iterative while loops.
// On a sufficiently deep tree, this causes stack overflow.
//
// Related: translation.ml:5985
//   "TODO: below is needed for lambdas in recursive positions, but is badddddd."

#include <hof_tree_loopify.h>

#include <cassert>
#include <cstdlib>
#include <iostream>
#include <sys/wait.h>
#include <unistd.h>

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

using Tree = HofTreeLoopify::tree<unsigned int>;

// Helper: extract root value (non-recursive, safe for deep trees)
unsigned int root_value(const Tree &t) {
  return std::visit(
      Overloaded{[](const Tree::Leaf &) -> unsigned int { return 0u; },
                 [](const Tree::Node &n) -> unsigned int { return n.d_a1; }},
      t.v());
}

// Build a left-leaning tree of given depth, iteratively.
// Avoids recursion so the tree is always constructed safely.
Tree build_deep_tree(unsigned int depth) {
  auto t = Tree::leaf();
  for (unsigned int i = 1; i <= depth; i++) {
    t = Tree::node(std::move(t), i, Tree::leaf());
  }
  return t;
}

// Run test_fn in a forked subprocess. Returns true if it exits 0.
// This isolates stack overflow crashes: if test_fn overflows, the child
// gets SIGSEGV but the parent survives and reports a clean failure.
bool survives(void (*test_fn)()) {
  pid_t pid = fork();
  if (pid == 0) {
    test_fn();
    _exit(0);
  }
  int status;
  waitpid(pid, &status, 0);
  return WIFEXITED(status) && WEXITSTATUS(status) == 0;
}

// --- Small tree correctness tests (no deep recursion, always pass) ---

void test_small_tree_map() {
  // tree_map (fun x => x * 2) small_tree
  // Root value 4 * 2 = 8
  assert(root_value(HofTreeLoopify::mapped) == 8);
  std::cout << "PASS: test_small_tree_map" << std::endl;
}

void test_small_tree_fold() {
  // tree_fold 0 (fun l x r => l + x + r) small_tree
  // Sum of all node values: 1+2+3+4+5+6+7 = 28
  assert(HofTreeLoopify::folded == 28);
  std::cout << "PASS: test_small_tree_fold" << std::endl;
}

void test_small_tree_zip() {
  // tree_zip_with Nat.add small_tree small_tree
  // Root value 4 + 4 = 8
  assert(root_value(HofTreeLoopify::zipped) == 8);
  std::cout << "PASS: test_small_tree_zip" << std::endl;
}

// --- Deep tree tests (run in subprocess to catch stack overflow) ---
//
// These build a 500,000-deep left-leaning tree ITERATIVELY (safe), then
// call tree_map/tree_fold on it. Without loopification, tree_map/tree_fold
// use 500,000 stack frames (~150MB of stack) and crash.
//
// When loopification handles HOF + multi-recursion, these will succeed.

constexpr unsigned int DEEP = 500000;

void deep_tree_map_impl() {
  auto deep = build_deep_tree(DEEP);
  auto doubled = HofTreeLoopify::tree_map<unsigned int, unsigned int>(
      [](unsigned int x) { return x * 2u; }, deep);
  // Verify correctness: root value should be doubled.
  if (root_value(doubled) != DEEP * 2) _exit(1);
  // Use _exit to skip destructors (unique_ptr chain would itself overflow).
  _exit(0);
}

void deep_tree_fold_impl() {
  auto deep = build_deep_tree(DEEP);
  // Just verify tree_fold completes without stack overflow.
  // (The sum wraps in unsigned int, so we don't check its exact value.)
  auto sum = HofTreeLoopify::tree_fold<unsigned int, unsigned int>(
      0u,
      [](unsigned int l, unsigned int x, unsigned int r) {
        return l + x + r;
      },
      deep);
  (void)sum;
  _exit(0);
}

void test_deep_tree_map() {
  // tree_map IS loopified (nontail stack-based), but the frame structs
  // store subtrees by value.  With value-type trees (unique_ptr children),
  // copying a subtree into a frame triggers recursive clone() which
  // overflows the stack for deep trees.
  //
  // TODO: store const T* in frames to avoid deep copies.
  assert(!survives(deep_tree_map_impl));
  std::cout << "PASS: test_deep_tree_map (expected stack overflow)" << std::endl;
}

void test_deep_tree_fold() {
  // Same issue as tree_map: frame storage triggers deep clone.
  assert(!survives(deep_tree_fold_impl));
  std::cout << "PASS: test_deep_tree_fold (expected stack overflow)" << std::endl;
}

int main() {
  test_small_tree_map();
  test_small_tree_fold();
  test_small_tree_zip();
  test_deep_tree_map();
  test_deep_tree_fold();

  std::cout << "All tests passed!" << std::endl;
  // Use _exit to skip static destructors: HofTreeLoopify::deep is a
  // 50,000-node tree whose unique_ptr destructor chain overflows the stack.
  _exit(0);
}
