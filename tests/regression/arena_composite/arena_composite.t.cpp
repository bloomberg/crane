// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
// Scoped-arena redesign regression: the composite-hang shape.
//
// A self-recursive value type (Comp::expr) stored inside an FMapAVL-shaped
// persistent balanced tree (Comp::avl) whose insert rebalances, all built
// inside ONE crane::arena_scope.  Under the old per-type arena representation
// this hung (every rebalance-triggered node copy deep-arena_clone'd the whole
// stored expr); with the redesign copying a node/expr is an O(1) refcount bump,
// so the workload must complete in bounded time with correct results.
#include <arena_composite.h>

#include <chrono>
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
using Comp_ = Comp;
using expr = Comp::expr;
using avl = Comp::avl;

// -- Unary Nat helpers -------------------------------------------------------
Nat mk_nat(long n) {
  Nat r = Nat::o();
  for (long i = 0; i < n; ++i) r = Nat::s(std::move(r));
  return r;
}
long nat_to_long(const Nat &n) {
  long c = 0;
  const Nat *cur = &n;
  Nat hold;
  while (std::holds_alternative<typename Nat::S>(cur->v())) {
    const auto &s = std::get<typename Nat::S>(cur->v());
    hold = *s.a0; // copy one level down (O(1) alias copy)
    cur = &hold;
    ++c;
  }
  return c;
}

// Balanced add-tree of depth d whose leaves are all lit(1): eval == 2^d,
// esize == 2^(d+1)-1.  A non-trivial self-recursive value to store and copy.
expr base_expr(int d) {
  if (d == 0) return expr::lit(mk_nat(1));
  return expr::add(base_expr(d - 1), base_expr(d - 1));
}
} // namespace

int main() {
  auto t_start = std::chrono::steady_clock::now();
  {
    crane::arena_scope s; // the ONLY thing that makes any of this arena-backed

    const int base_depth = 5; // eval == 32, esize == 63
    const long base_eval = 32;
    expr base = base_expr(base_depth);
    ASSERT(nat_to_long(base.eval()) == base_eval);
    ASSERT(nat_to_long(base.esize()) == 63);

    // Insert K keys, each mapped to add(lit(k), base) -- a fresh self-recursive
    // value per key that shares `base`'s nodes (O(1) copies).  Sequential
    // insertion into the AVL maximizes rebalancing (and thus subtree/expr
    // copying), which is exactly the composite copy path that used to hang.
    const long K = 80;
    avl m = avl::leaf();
    for (long k = 0; k < K; ++k) {
      expr v = expr::add(expr::lit(mk_nat(k)), base); // eval == k + base_eval
      m = m.insert(mk_nat(k), std::move(v));
    }

    // Structure is intact: exactly K distinct keys survived all rebalances.
    ASSERT(nat_to_long(m.size()) == K);

    // Every stored value is correct after all the rebalance-driven copying.
    for (long k = 0; k < K; ++k) {
      expr got = m.find(mk_nat(k));
      ASSERT(nat_to_long(got.eval()) == k + base_eval);
      ASSERT(nat_to_long(got.esize()) == 1 /*add*/ + 1 /*lit*/ + 63 /*base*/);
    }

    // A missing key returns the extraction's default (lit 0).
    ASSERT(nat_to_long(m.find(mk_nat(K + 5)).eval()) == 0);

    // Copying the whole map is an O(1) per-node refcount bump, not a deep clone.
    avl m2 = m;
    ASSERT(nat_to_long(m2.size()) == K);
    ASSERT(nat_to_long(m2.find(mk_nat(7)).eval()) == 7 + base_eval);
  } // arena_scope closes: region freed once every handle above is gone.

  auto elapsed = std::chrono::duration_cast<std::chrono::seconds>(
                     std::chrono::steady_clock::now() - t_start)
                     .count();
  // Bounded time: the old composite-hang would blow far past this; even with
  // unary-Nat overhead the redesigned O(1) copies finish in well under 30s.
  ASSERT(elapsed < 30);

  if (testStatus > 0)
    std::cerr << "arena_composite: " << testStatus << " test(s) FAILED\n";
  return testStatus;
}
