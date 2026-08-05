// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
// Test for opt-in arena extraction (Crane Arena Tree.tree).
#include <arena_tree.h>

#include <iostream>
#include <variant>

// ============================================================================
//                     STANDARD BDE ASSERT TEST FUNCTION
// ----------------------------------------------------------------------------
namespace {
int testStatus = 0;
void aSsErT(bool condition, const char *message, int line) {
  if (condition) {
    std::cout << "Error " __FILE__ "(" << line << "): " << message
              << "    (failed)" << std::endl;
    if (0 <= testStatus && testStatus <= 100) ++testStatus;
  }
}
} // namespace
#define ASSERT(X) aSsErT(!(X), #X, __LINE__);

namespace {
using T = Tree<long long>;

long count(const T &t) {
  if (std::holds_alternative<typename T::Leaf>(t.v())) return 1;
  const auto &n = std::get<typename T::Node>(t.v());
  return 1 + count(*n.t1) + count(*n.t2);
}

// full binary tree of depth d (built in the given arena)
T build(crane::arena &a, int d) {
  if (d == 0) return T::leaf();
  return T::node(a, build(a, d - 1), (long long)d, build(a, d - 1));
}

// value at the root's node (undefined on a leaf)
long long root_val(const T &t) {
  return std::get<typename T::Node>(t.v()).x;
}
} // namespace

int main() {
  {
    crane::arena_scope s;
    crane::arena &a = crane::current_arena();

    // leaf / node discrimination
    ASSERT(T::leaf().is_leaf() == Bool0::TRUE_);
    T n = T::node(a, T::leaf(), 42, T::leaf());
    ASSERT(n.is_leaf() == Bool0::FALSE_);
    ASSERT(root_val(n) == 42);

    // sizes of full trees: depth d has 2^(d+1)-1 nodes
    ASSERT(count(build(a, 0)) == 1);
    ASSERT(count(build(a, 3)) == 15);
    ASSERT(count(build(a, 10)) == 2047);

    // Milestone 2: mirror()'s generated body threads an explicit
    // crane::arena& through to its calls to Tree<A>::node(...), so it can
    // be called here with the arena argument like any other arena-mode
    // method.
    T t = T::node(a, T::node(a, T::leaf(), 1, T::leaf()), 2,
                  T::node(a, T::leaf(), 3, T::leaf()));
    T m = t.mirror(a);
    ASSERT(count(m) == count(t));
    ASSERT(root_val(m) == 2);
    // after mirror, left child holds what was the right child (value 3)
    const auto &mn = std::get<typename T::Node>(m.v());
    ASSERT(root_val(*mn.t1) == 3);
    ASSERT(root_val(*mn.t2) == 1);

    // Copying an arena-mode value must deep-copy the node graph, not alias
    // the source's raw pointers (arena.h documents this as the required
    // copy semantics for arena-mode handles; the implicit compiler-generated
    // copy constructor would otherwise just copy the raw pointers verbatim).
    T orig = build(a, 3);
    T copy_of_orig = orig; // exercises the explicit deep-copy constructor
    ASSERT(count(copy_of_orig) == count(orig));
    const auto &orig_n = std::get<typename T::Node>(orig.v());
    const auto &copy_n = std::get<typename T::Node>(copy_of_orig.v());
    // Same values, but the recursive-field pointers are pointer-distinct:
    // the copy lives in nodes of its own, not aliases into orig's nodes.
    ASSERT(orig_n.t1 != copy_n.t1);
    ASSERT(orig_n.t2 != copy_n.t2);
    ASSERT(root_val(*orig_n.t1) == root_val(*copy_n.t1));
    ASSERT(root_val(*orig_n.t2) == root_val(*copy_n.t2));
    // Rebuilding one instance must not affect the other (no shared state).
    copy_of_orig = T::leaf();
    ASSERT(copy_of_orig.is_leaf() == Bool0::TRUE_);
    ASSERT(orig.is_leaf() == Bool0::FALSE_);
    ASSERT(count(orig) == 15);
  } // arena dropped here — frees all nodes in O(1)

  if (testStatus > 0)
    std::cerr << "arena_tree: " << testStatus << " test(s) FAILED\n";
  return testStatus;
}
