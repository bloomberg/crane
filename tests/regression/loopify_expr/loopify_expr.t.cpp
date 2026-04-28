// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <loopify_expr.h>

#include <functional>
#include <iostream>
#include <memory>
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

    if (0 <= testStatus && testStatus <= 100) {
      ++testStatus;
    }
  }
}

} // namespace

#define ASSERT(X) aSsErT(!(X), #X, __LINE__);

int main() {
  using Expr = LoopifyExpr::expr;

  // Build: Add(Val(1), Mul(Val(2), Val(3)))
  auto e = Expr::add(
      Expr::val(1u),
      Expr::mul(Expr::val(2u), Expr::val(3u)));

  // eval(Add(Val(1), Mul(Val(2), Val(3)))) = 1 + 2*3 = 7
  ASSERT(e.eval() == 7u);

  // depth(Add(Val(1), Mul(Val(2), Val(3)))) = 1 + max(0, 1+max(0,0)) = 2
  ASSERT(e.depth() == 2u);

  // count_vals = 3
  ASSERT(e.count_vals() == 3u);

  // Test Succ
  auto succ_e = Expr::succ(Expr::val(5u));
  ASSERT(succ_e.eval() == 6u);
  ASSERT(succ_e.depth() == 1u);

  // Test size: Add(Val(1), Mul(Val(2), Val(3))) = 1 + 1 + (1 + 1 + 1) = 5
  ASSERT(e.size() == 5u);

  // Test simplify: Add(Val(0), Val(5)) => Val(5)
  auto add_zero = Expr::add(Expr::val(0u), Expr::val(5u));
  auto simplified = add_zero.simplify();
  ASSERT(simplified.eval() == 5u);
  // Should be just Val(5), so size=1
  ASSERT(simplified.size() == 1u);

  // Test simplify: Mul(Val(1), Add(Val(2), Val(3))) => Add(Val(2), Val(3))
  auto mul_one = Expr::mul(
      Expr::val(1u),
      Expr::add(Expr::val(2u), Expr::val(3u)));
  auto simplified2 = mul_one.simplify();
  ASSERT(simplified2.eval() == 5u);
  ASSERT(simplified2.size() == 3u); // Add(Val(2), Val(3))

  // Test simplify: Mul(Val(0), big_expr) => Val(0)
  auto mul_zero = Expr::mul(Expr::val(0u), e);
  auto simplified3 = mul_zero.simplify();
  ASSERT(simplified3.eval() == 0u);
  ASSERT(simplified3.size() == 1u);

  return testStatus;
}
