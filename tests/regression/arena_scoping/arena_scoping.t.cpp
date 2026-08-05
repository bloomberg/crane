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
  crane::arena &a = crane::current_arena();
  return T::node(a, build(d - 1), (long long)d, build(d - 1));
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

  // -- (b) Fallback-growth warning: scoped is silent, unscoped warns ---------
  // The warning is debug-only (#ifndef NDEBUG) and fires once per thread the
  // first time the never-resetting fallback arena is reached. Do the scoped
  // capture first (must stay silent and must not consume the one-shot), then
  // the unscoped capture (must trip the fallback and warn).
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
          // No scope installed: allocations land in the fallback arena.
          (void)build(3);
        },
        "arena_scoping_unscoped.err");
#ifndef NDEBUG
    ASSERT(unscoped_err.find("fallback") != std::string::npos);
#else
    ASSERT(unscoped_err.empty());
#endif
  }

  if (testStatus > 0)
    std::cerr << "arena_scoping: " << testStatus << " test(s) FAILED\n";
  return testStatus;
}
