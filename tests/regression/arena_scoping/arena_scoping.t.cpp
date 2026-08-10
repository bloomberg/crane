// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
// Test for caller-owned scoped arenas (crane::arena_use_scope) and the
// debug-build fallback-growth warning.
#include <arena_scoping.h>

#include <cstdio>
#include <fstream>
#include <functional>
#include <iostream>
#include <iterator>
#include <string>
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

// Count nodes by chasing the raw child pointers into the arena.
long count(const T &t) {
  if (std::holds_alternative<typename T::Leaf>(t.v())) return 1;
  const auto &n = std::get<typename T::Node>(t.v());
  return 1 + count(*n.t1) + count(*n.t2);
}

// full binary tree of depth d, built in whatever arena is currently installed
T build(int d) {
  if (d == 0) return T::leaf();
  return T::node(build(d - 1), (long long)d, build(d - 1));
}

// Capture everything written to stderr while running f() into a string.
std::string capture_stderr(const std::function<void()> &f, const char *path) {
  std::fflush(stderr);
  FILE *r = std::freopen(path, "w", stderr);
  (void)r;
  f();
  std::fflush(stderr);
  std::ifstream ifs(path);
  return std::string((std::istreambuf_iterator<char>(ifs)),
                     std::istreambuf_iterator<char>());
}
} // namespace

int main() {
  // -- (a) One caller-owned arena reused across two arena_use_scopes ---------
  // Both trees must remain valid *simultaneously* after both scopes exit,
  // because the arena (which owns their nodes) outlives both scopes.
  {
    crane::arena shared;
    T t1;
    T t2;
    {
      crane::arena_use_scope us(shared);
      t1 = build(3); // 2^4 - 1 = 15 nodes
    }
    {
      crane::arena_use_scope us(shared);
      t2 = build(4); // 2^5 - 1 = 31 nodes
    }
    // Both scopes are gone, but `shared` still owns every node.
    ASSERT(count(t1) == 15);
    ASSERT(count(t2) == 31);
    // A nested (non-owning) scope restores the previous current-arena on exit.
    {
      crane::arena other;
      {
        crane::arena_use_scope inner(other);
        (void)build(2);
      }
      crane::arena_use_scope us(shared);
      T t3 = build(2); // 7 nodes, back in `shared`
      ASSERT(count(t3) == 7);
    }
  } // `shared` and `other` dropped here: O(1) bulk free of all nodes.

  // -- (b) No spurious warnings ---------------------------------------------
  // Scoped-arena redesign: generated factories never touch the never-resetting
  // fallback arena.  With a caller-owned scope installed, allocations go to that
  // region; with NO scope, allocations go to the plain heap (make_shared), not
  // the fallback arena.  Both must be silent (the fallback-growth warning must
  // not fire for ordinary generated code either way).
  {
    std::string scoped_err = capture_stderr(
        [] {
          crane::arena a;
          crane::arena_use_scope us(a);
          (void)build(3);
        },
        "arena_scoping_scoped.err");
    ASSERT(scoped_err.find("fallback") == std::string::npos);

    std::string unscoped_err = capture_stderr(
        [] {
          // No scope installed: allocations are plain-heap and silent (the new
          // safe default; previously arena-mode types would have grown the
          // fallback region and warned).
          (void)build(3);
        },
        "arena_scoping_unscoped.err");
    ASSERT(unscoped_err.find("fallback") == std::string::npos);
  }

  // -- (c) Scoped-arena redesign: NO arena type annotation + an open owning
  //        crane::arena_scope ==> the value is arena-backed, may safely escape
  //        the scope (region kept alive by the shared keeper), and its payload
  //        bypasses the heap.  Under the pre-redesign model this exact
  //        combination (a type with no `Crane Arena` directive) was a silent
  //        no-op; this is the new behavior the redesign introduces.
  {
    // (c1) Observable arena-backing: the SAME build, with NO type-level arena
    //      annotation, bump-allocates every node from the region when a scope
    //      is open and bump-allocates NONE when no scope is open.  The runtime
    //      [arena_bump_count] is a direct, allocator-agnostic witness.
    const int d = 10;                 // 2^11 - 1 = 2047 nodes
    // Every node except the root is reached through exactly one recursive-field
    // smart pointer, i.e. exactly one arena_make_shared call; the root is the
    // returned stack value.
    const unsigned long long expected_bumps = ((1ULL << (d + 1)) - 1) - 1;

    unsigned long long before_no_scope = crane::arena_bump_count();
    { T outside = build(d); (void)count(outside); }
    // No scope: nothing is arena-backed (this is the plain-heap fallback, the
    // exact case that used to be a silent no-op for un-annotated types).
    ASSERT(crane::arena_bump_count() == before_no_scope);

    unsigned long long before_in_scope = crane::arena_bump_count();
    {
      crane::arena_scope s;
      T inside = build(d);
      (void)count(inside);
    }
    // In scope: every non-root node was bump-allocated from the region.
    ASSERT(crane::arena_bump_count() - before_in_scope == expected_bumps);

    // (c2) Escape safety: a value built inside an owning scope stays fully
    //      valid after the scope closes (the region is kept alive by the
    //      keeper the escaped value carries), and is freed only when the last
    //      reference drops.
    T escaped;
    {
      crane::arena_scope s;
      escaped = build(5); // 63 nodes bump-allocated in s's region
      ASSERT(count(escaped) == 63);
    } // owning scope closes; `escaped` must remain valid.
    ASSERT(count(escaped) == 63);
    T aliased = escaped;         // O(1) aliasing copy, same region
    ASSERT(count(aliased) == 63);
    escaped = T::leaf();         // rebind one handle; the other is unaffected
    ASSERT(count(aliased) == 63);
  } // last reference drops here → region freed

  if (testStatus > 0)
    std::cerr << "arena_scoping: " << testStatus << " test(s) FAILED\n";
  return testStatus;
}
