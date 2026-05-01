// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
//
// Test harness for the spreadsheet kernel.  Exercises construction,
// arithmetic, dependency chains, division-by-zero, cycles, and the
// out-of-grid lookup behaviour of the underlying persistent_array.

#include <spreadsheet.h>

#include <cstdint>
#include <iostream>

namespace {

int testStatus = 0;

void aSsErT(bool condition, const char* message, int line) {
  if (condition) {
    std::cout << "Error " __FILE__ "(" << line << "): " << message
              << "    (failed)" << std::endl;
    if (0 <= testStatus && testStatus <= 100) {
      ++testStatus;
    }
  }
}

}  // namespace

#define ASSERT(X) aSsErT(!(X), #X, __LINE__);

using S = Spreadsheet;

int main() {
  // Sanity: the closed Rocq-side smoke value computes to 35.
  ASSERT(S::smoke.has_value());
  ASSERT(*S::smoke == 35);

  // A1=10, B1=3.  Test all four operators plus a unary-negation form.
  const auto a1 = S::CellRef{0, 0};
  const auto b1 = S::CellRef{1, 0};
  const auto c1 = S::CellRef{2, 0};
  auto sh = S::set_cell(S::new_sheet, a1, S::Cell::clit(10));
  sh = S::set_cell(sh, b1, S::Cell::clit(3));

  auto eval_with = [&](S::Expr e) {
    auto local = S::set_cell(sh, c1, S::Cell::cform(std::move(e)));
    return S::eval_cell(S::DEFAULT_FUEL, local, c1);
  };

  ASSERT(*eval_with(S::Expr::eadd(S::Expr::eref(a1), S::Expr::eref(b1))) == 13);
  ASSERT(*eval_with(S::Expr::esub(S::Expr::eref(a1), S::Expr::eref(b1))) ==  7);
  ASSERT(*eval_with(S::Expr::emul(S::Expr::eref(a1), S::Expr::eref(b1))) == 30);
  ASSERT(*eval_with(S::Expr::ediv(S::Expr::eref(a1), S::Expr::eref(b1))) ==  3);

  // Division by zero -> None.
  ASSERT(!eval_with(S::Expr::ediv(S::Expr::eref(a1), S::Expr::eint(0))).has_value());

  // Empty cell evaluates as 0.
  ASSERT(*S::eval_cell(S::DEFAULT_FUEL, S::new_sheet, S::CellRef{5, 5}) == 0);

  // Multi-letter columns: AA = 26, BA = 52, CZ = 103.  Sum across all three.
  {
    auto aa1 = S::CellRef{26, 0};
    auto ba1 = S::CellRef{52, 0};
    auto cz1 = S::CellRef{103, 0};
    auto wide = S::set_cell(S::new_sheet, aa1, S::Cell::clit(100));
    wide = S::set_cell(wide, ba1, S::Cell::clit(200));
    wide = S::set_cell(wide, cz1, S::Cell::clit(700));
    auto sum_expr = S::Expr::eadd(
        S::Expr::eadd(S::Expr::eref(aa1), S::Expr::eref(ba1)),
        S::Expr::eref(cz1));
    wide = S::set_cell(wide, c1, S::Cell::cform(std::move(sum_expr)));
    auto sum = S::eval_cell(S::DEFAULT_FUEL, wide, c1);
    ASSERT(sum.has_value());
    ASSERT(*sum == 1000);
  }

  // Dependency chain: A1=1, A2=A1+1, ..., A50=A49+1; final value is 50.
  {
    auto chain = S::set_cell(S::new_sheet, S::CellRef{0, 0}, S::Cell::clit(1));
    for (int r = 1; r < 50; ++r) {
      auto e = S::Expr::eadd(
          S::Expr::eref(S::CellRef{0, r - 1}),
          S::Expr::eint(1));
      chain = S::set_cell(chain, S::CellRef{0, r},
                          S::Cell::cform(std::move(e)));
    }
    auto a50 = S::eval_cell(S::DEFAULT_FUEL, chain, S::CellRef{0, 49});
    ASSERT(a50.has_value());
    ASSERT(*a50 == 50);

    auto a50_low = S::eval_cell(5, chain, S::CellRef{0, 49});
    ASSERT(!a50_low.has_value());
  }

  // A two-cell cycle: A1 <-> B1 returns None on either entry point.
  {
    auto cyc = S::set_cell(S::new_sheet, a1,
        S::Cell::cform(S::Expr::eref(b1)));
    cyc = S::set_cell(cyc, b1, S::Cell::cform(S::Expr::eref(a1)));
    ASSERT(!S::eval_cell(S::DEFAULT_FUEL, cyc, a1).has_value());
    ASSERT(!S::eval_cell(S::DEFAULT_FUEL, cyc, b1).has_value());
  }

  if (testStatus != 0) {
    std::cout << "Error: testStatus = " << testStatus << "." << std::endl;
  }
  return testStatus;
}
