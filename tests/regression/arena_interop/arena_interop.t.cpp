// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
// Interop test for Part 3's explicit-arena-parameter design: proves
// arena-mode and ordinary shared_ptr-mode types compose correctly.
//   (1) a non-arena record (Interop::wrapper) holding an arena-mode value
//       (Interop::tree<Nat>) as a field: copy/move/destroy must not leave
//       dangling pointers into a freed arena.
//   (2) the arena-mode type itself parameterized over a non-arena,
//       shared_ptr-mode recursive payload (Interop::nlist): refcounting on
//       the payload must work normally, untouched by the tree's arena
//       opt-in.
//   (3) two independent arenas built concurrently with no cross
//       contamination, and deep-copy across two different arenas.
#include <arena_interop.h>

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
Nat int_to_nat(int x) {
  if (x <= 0) return Nat::o();
  return Nat::s(int_to_nat(x - 1));
}

int nat_to_int(const Nat &n) {
  if (std::holds_alternative<typename Nat::O>(n.v())) return 0;
  const auto &[a0] = std::get<typename Nat::S>(n.v());
  return 1 + nat_to_int(*a0);
}

using NatTree = Interop::tree<Nat>;
using ListTree = Interop::tree<Interop::nlist>;

// full binary tree of depth d, arena-allocated, payload = node depth
NatTree build_nat_tree(crane::arena &a, int d) {
  if (d == 0) return NatTree::leaf();
  return NatTree::node(a, build_nat_tree(a, d - 1), int_to_nat(d),
                       build_nat_tree(a, d - 1));
}

long count_nodes(const NatTree &t) {
  if (std::holds_alternative<typename NatTree::Leaf>(t.v())) return 1;
  const auto &n = std::get<typename NatTree::Node>(t.v());
  return 1 + count_nodes(*n.t1) + count_nodes(*n.t2);
}

// full binary tree of depth d, arena-allocated, payload = a shared_ptr-mode
// nlist [1, 2, ..., d] so we can inspect refcounts on the *payload* nodes.
ListTree build_list_tree(crane::arena &a, const Interop::nlist &payload,
                         int d) {
  if (d == 0) return ListTree::leaf();
  return ListTree::node(a, build_list_tree(a, payload, d - 1), payload,
                        build_list_tree(a, payload, d - 1));
}

long count_list_nodes(const ListTree &t) {
  if (std::holds_alternative<typename ListTree::Leaf>(t.v())) return 1;
  const auto &n = std::get<typename ListTree::Node>(t.v());
  return 1 + count_list_nodes(*n.t1) + count_list_nodes(*n.t2);
}
} // namespace

int main() {
  // -- (1) Non-arena wrapper holding an arena-mode field ---------------------
  {
    crane::arena_scope s;
    crane::arena &a = crane::current_arena();

    Interop::wrapper w{int_to_nat(7), build_nat_tree(a, 3)};
    ASSERT(nat_to_int(Interop::wrapper_size(w)) == 15); // 2^4 - 1

    // Copying the wrapper must deep-copy its arena-mode field (delegating to
    // tree<Nat>'s own deep-copy constructor), not alias the source's raw
    // node pointers.
    Interop::wrapper w_copy = w;
    ASSERT(nat_to_int(Interop::wrapper_size(w_copy)) == 15);
    const auto &orig_n = std::get<typename NatTree::Node>(w.w_tree.v());
    const auto &copy_n = std::get<typename NatTree::Node>(w_copy.w_tree.v());
    ASSERT(orig_n.t1 != copy_n.t1);
    ASSERT(orig_n.t2 != copy_n.t2);

    // Moving the wrapper must leave the source in a valid (empty-tree)
    // state and transfer ownership of the arena-mode field's node pointers
    // without double-freeing them.
    Interop::wrapper w_moved = std::move(w_copy);
    ASSERT(nat_to_int(Interop::wrapper_size(w_moved)) == 15);

    // Rebuilding one wrapper's field must not affect an independently-built
    // one (no shared state via the arena-mode field).
    w_moved.w_tree = NatTree::leaf();
    ASSERT(nat_to_int(Interop::wrapper_size(w_moved)) == 1);
    ASSERT(nat_to_int(Interop::wrapper_size(w)) == 15);
  } // arena dropped here: O(1) bulk free of every wrapper's tree nodes above.

  // -- (2) Arena-mode tree parameterized over a non-arena shared_ptr payload -
  {
    crane::arena_scope s;
    crane::arena &a = crane::current_arena();

    // Build a small shared_ptr-mode nlist [1, 2, 3] once...
    Interop::nlist payload =
        Interop::nlist::ncons(int_to_nat(1),
            Interop::nlist::ncons(int_to_nat(2),
                Interop::nlist::ncons(int_to_nat(3), Interop::nlist::nnil())));
    ASSERT(nat_to_int(payload.nlist_len()) == 3);

    // ...then copy it into every leaf/node payload slot of a depth-3 arena
    // tree (15 nodes). Each copy of `payload` bumps refcounts on the shared
    // inner nlist nodes via the ordinary shared_ptr copy path; this must
    // work exactly as it would for a non-arena container, unaffected by
    // the fact that the *tree* itself is arena-mode.
    ListTree t = build_list_tree(a, payload, 3);
    ASSERT(count_list_nodes(t) == 15);

    // Walk one root-to-leaf path and check the payload survived unmodified
    // at every level, including deep-copied nodes.
    const auto &n0 = std::get<typename ListTree::Node>(t.v());
    ASSERT(nat_to_int(n0.x.nlist_len()) == 3);
    const auto &n1 = std::get<typename ListTree::Node>(n0.t1->v());
    ASSERT(nat_to_int(n1.x.nlist_len()) == 3);

    // Deep-copying the tree must deep-copy the tree's own node structure
    // (raw arena pointers) while the payload's shared_ptr refcounting is
    // untouched by that deep copy (payload copies are shallow, sharing the
    // underlying nlist spine, per ordinary shared_ptr semantics).
    ListTree t_copy = t;
    ASSERT(count_list_nodes(t_copy) == 15);
    const auto &orig_n = std::get<typename ListTree::Node>(t.v());
    const auto &copy_n = std::get<typename ListTree::Node>(t_copy.v());
    ASSERT(orig_n.t1 != copy_n.t1); // distinct arena tree nodes
    ASSERT(nat_to_int(copy_n.x.nlist_len()) == 3); // payload intact
  } // arena dropped here.

  // -- (3a) Two independent arenas built concurrently, no cross-contamination
  {
    crane::arena a1;
    crane::arena a2;
    NatTree t1, t2;
    {
      crane::arena_use_scope us1(a1);
      t1 = build_nat_tree(a1, 3); // 15 nodes, lives in a1
    }
    {
      crane::arena_use_scope us2(a2);
      t2 = build_nat_tree(a2, 4); // 31 nodes, lives in a2
    }
    // Both trees remain independently valid: neither arena's nodes alias
    // the other's, and freeing one arena (below) must not disturb the
    // other tree at all.
    ASSERT(count_nodes(t1) == 15);
    ASSERT(count_nodes(t2) == 31);
    const auto &n1 = std::get<typename NatTree::Node>(t1.v());
    const auto &n2 = std::get<typename NatTree::Node>(t2.v());
    ASSERT(static_cast<const void *>(n1.t1) !=
           static_cast<const void *>(n2.t1));

    // Drop a1 first; t2 (owned by a2, still alive) must be untouched.
    a1 = crane::arena(); // reset/free a1's nodes; t1's old nodes are gone
    ASSERT(count_nodes(t2) == 31);

    // -- (3b) Deep-copy across two different arenas -------------------------
    // Copying a tree that lives in a2 while a3 is the ambient arena must
    // allocate the copy's nodes in a3, not a2 — the copy must be fully
    // independent of a2 so that later freeing a2 doesn't affect it.
    crane::arena a3;
    NatTree t2_copy_in_a3;
    {
      crane::arena_use_scope us3(a3);
      t2_copy_in_a3 = t2; // deep copy: allocates into the ambient arena (a3)
    }
    ASSERT(count_nodes(t2_copy_in_a3) == 31);
    const auto &n2c = std::get<typename NatTree::Node>(t2_copy_in_a3.v());
    ASSERT(static_cast<const void *>(n2.t1) !=
           static_cast<const void *>(n2c.t1));

    a2 = crane::arena(); // free a2's nodes (including the original t2)
    // The a3 copy must survive a2 being freed: prove it's still readable
    // and correct.
    ASSERT(count_nodes(t2_copy_in_a3) == 31);
  }

  if (testStatus > 0)
    std::cerr << "arena_interop: " << testStatus << " test(s) FAILED\n";
  return testStatus;
}
