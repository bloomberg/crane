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

// full binary tree of depth d (built in the ambient arena)
T build(int d) {
  if (d == 0) return T::leaf();
  return T::node(build(d - 1), (long long)d, build(d - 1));
}

// value at the root's node (undefined on a leaf)
long long root_val(const T &t) {
  return std::get<typename T::Node>(t.v()).x;
}
} // namespace

int main() {
  {
    crane::arena_scope s;

    // leaf / node discrimination
    ASSERT(T::leaf().is_leaf() == Bool0::TRUE_);
    T n = T::node(T::leaf(), 42, T::leaf());
    ASSERT(n.is_leaf() == Bool0::FALSE_);
    ASSERT(root_val(n) == 42);

    // sizes of full trees: depth d has 2^(d+1)-1 nodes
    ASSERT(count(build(0)) == 1);
    ASSERT(count(build(3)) == 15);
    ASSERT(count(build(10)) == 2047);

    // mirror preserves node count and swaps children
    T t = T::node(T::node(T::leaf(), 1, T::leaf()), 2,
                  T::node(T::leaf(), 3, T::leaf()));
    T m = t.mirror();
    ASSERT(count(m) == count(t));
    ASSERT(root_val(m) == 2);
    // after mirror, left child holds what was the right child (value 3)
    const auto &mn = std::get<typename T::Node>(m.v());
    ASSERT(root_val(*mn.t1) == 3);
    ASSERT(root_val(*mn.t2) == 1);

    // Scoped-arena redesign: recursive fields are ordinary refcounted smart
    // pointers, so copying an arena-backed value is an O(1) refcount bump that
    // *aliases* the source's nodes (safe: Coq values are immutable, and the
    // shared arena keeper keeps the region alive as long as any copy exists).
    // This replaces the old deep-copy-into-a-fresh-region semantics; deleting
    // that deep copy is exactly what removes the composite-hang failure mode.
    T orig = build(3);
    T copy_of_orig = orig; // O(1) aliasing copy (refcount bump)
    ASSERT(count(copy_of_orig) == count(orig));
    const auto &orig_n = std::get<typename T::Node>(orig.v());
    const auto &copy_n = std::get<typename T::Node>(copy_of_orig.v());
    // The copy shares the source's nodes: the recursive-field pointers are now
    // pointer-EQUAL (aliased), not distinct.
    ASSERT(orig_n.t1 == copy_n.t1);
    ASSERT(orig_n.t2 == copy_n.t2);
    ASSERT(root_val(*orig_n.t1) == root_val(*copy_n.t1));
    ASSERT(root_val(*orig_n.t2) == root_val(*copy_n.t2));
    // Rebinding one handle must not affect the other: assignment rebinds this
    // handle's smart pointers only, leaving the source's untouched.
    copy_of_orig = T::leaf();
    ASSERT(copy_of_orig.is_leaf() == Bool0::TRUE_);
    ASSERT(orig.is_leaf() == Bool0::FALSE_);
    ASSERT(count(orig) == 15);
  } // arena dropped here — frees all nodes in O(1)

  if (testStatus > 0)
    std::cerr << "arena_tree: " << testStatus << " test(s) FAILED\n";
  return testStatus;
}
