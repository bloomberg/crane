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
  auto e = Expr::ctor::Add_(
      Expr::ctor::Val_(1u),
      Expr::ctor::Mul_(Expr::ctor::Val_(2u), Expr::ctor::Val_(3u)));

  // eval(Add(Val(1), Mul(Val(2), Val(3)))) = 1 + 2*3 = 7
  ASSERT(LoopifyExpr::eval(e) == 7u);

  // depth(Add(Val(1), Mul(Val(2), Val(3)))) = 1 + max(0, 1+max(0,0)) = 2
  ASSERT(LoopifyExpr::depth(e) == 2u);

  // count_vals = 3
  ASSERT(LoopifyExpr::count_vals(e) == 3u);

  // Test Succ
  auto succ_e = Expr::ctor::Succ_(Expr::ctor::Val_(5u));
  ASSERT(LoopifyExpr::eval(succ_e) == 6u);
  ASSERT(LoopifyExpr::depth(succ_e) == 1u);

  // Test size: Add(Val(1), Mul(Val(2), Val(3))) = 1 + 1 + (1 + 1 + 1) = 5
  ASSERT(LoopifyExpr::size(e) == 5u);

  // Test simplify: Add(Val(0), Val(5)) => Val(5)
  auto add_zero = Expr::ctor::Add_(Expr::ctor::Val_(0u), Expr::ctor::Val_(5u));
  auto simplified = LoopifyExpr::simplify(add_zero);
  ASSERT(LoopifyExpr::eval(simplified) == 5u);
  // Should be just Val(5), so size=1
  ASSERT(LoopifyExpr::size(simplified) == 1u);

  // Test simplify: Mul(Val(1), Add(Val(2), Val(3))) => Add(Val(2), Val(3))
  auto mul_one = Expr::ctor::Mul_(
      Expr::ctor::Val_(1u),
      Expr::ctor::Add_(Expr::ctor::Val_(2u), Expr::ctor::Val_(3u)));
  auto simplified2 = LoopifyExpr::simplify(mul_one);
  ASSERT(LoopifyExpr::eval(simplified2) == 5u);
  ASSERT(LoopifyExpr::size(simplified2) == 3u); // Add(Val(2), Val(3))

  // Test simplify: Mul(Val(0), big_expr) => Val(0)
  auto mul_zero = Expr::ctor::Mul_(Expr::ctor::Val_(0u), e);
  auto simplified3 = LoopifyExpr::simplify(mul_zero);
  ASSERT(LoopifyExpr::eval(simplified3) == 0u);
  ASSERT(LoopifyExpr::size(simplified3) == 1u);

  return testStatus;
}
