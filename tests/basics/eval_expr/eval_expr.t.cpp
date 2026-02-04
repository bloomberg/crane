// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <eval_expr.h>

#include <functional>
#include <iostream>
#include <memory>
#include <string>
#include <variant>

// ============================================================================
//                     STANDARD BDE ASSERT TEST FUNCTION
// ----------------------------------------------------------------------------

namespace {

int testStatus = 0;

void aSsErT(bool condition, const char *message, int line)
{
    if (condition) {
        std::cout << "Error " __FILE__ "(" << line << "): " << message
             << "    (failed)" << std::endl;

        if (0 <= testStatus && testStatus <= 100) {
            ++testStatus;
        }
    }
}

}  // close unnamed namespace

#define ASSERT(X)                                              \
    aSsErT(!(X), #X, __LINE__);

int main() {
  std::cout << "Testing eval_expr extraction...\n";

  // Test 1: Simple natural number literal
  // eval (ENat 42) = 42
  auto e1 = Expr::expr::ctor::ENat_(42);
  auto r1 = e1->eval(Ty::ty::ctor::TNat_());
  ASSERT(std::any_cast<unsigned int>(r1) == 42);
  std::cout << "Test 1 passed: ENat 42 evaluates to 42\n";

  // Test 2: Simple boolean literal
  // eval (EBool true) = true
  auto e2 = Expr::expr::ctor::EBool_(true);
  auto r2 = e2->eval(Ty::ty::ctor::TBool_());
  ASSERT(std::any_cast<bool>(r2) == true);
  std::cout << "Test 2 passed: EBool true evaluates to true\n";

  // Test 3: Addition
  // eval (EAdd (ENat 10) (ENat 32)) = 42
  auto e3 = Expr::expr::ctor::EAdd_(
    Expr::expr::ctor::ENat_(10),
    Expr::expr::ctor::ENat_(32)
  );
  auto r3 = e3->eval(Ty::ty::ctor::TNat_());
  ASSERT(std::any_cast<unsigned int>(r3) == 42);
  std::cout << "Test 3 passed: 10 + 32 = 42\n";

  // Test 4: Equality (true case)
  // eval (EEq (ENat 5) (ENat 5)) = true
  auto e4 = Expr::expr::ctor::EEq_(
    Expr::expr::ctor::ENat_(5),
    Expr::expr::ctor::ENat_(5)
  );
  auto r4 = e4->eval(Ty::ty::ctor::TBool_());
  ASSERT(std::any_cast<bool>(r4) == true);
  std::cout << "Test 4 passed: 5 == 5 is true\n";

  // Test 5: Equality (false case)
  // eval (EEq (ENat 3) (ENat 7)) = false
  auto e5 = Expr::expr::ctor::EEq_(
    Expr::expr::ctor::ENat_(3),
    Expr::expr::ctor::ENat_(7)
  );
  auto r5 = e5->eval(Ty::ty::ctor::TBool_());
  ASSERT(std::any_cast<bool>(r5) == false);
  std::cout << "Test 5 passed: 3 == 7 is false\n";

  // Test 6: If-then-else (true branch)
  // eval (EIf TNat (EBool true) (ENat 100) (ENat 200)) = 100
  auto e6 = Expr::expr::ctor::EIf_(
    Ty::ty::ctor::TNat_(),
    Expr::expr::ctor::EBool_(true),
    Expr::expr::ctor::ENat_(100),
    Expr::expr::ctor::ENat_(200)
  );
  auto r6 = e6->eval(Ty::ty::ctor::TNat_());
  ASSERT(std::any_cast<unsigned int>(r6) == 100);
  std::cout << "Test 6 passed: if true then 100 else 200 = 100\n";

  // Test 7: If-then-else (false branch)
  // eval (EIf TNat (EBool false) (ENat 100) (ENat 200)) = 200
  auto e7 = Expr::expr::ctor::EIf_(
    Ty::ty::ctor::TNat_(),
    Expr::expr::ctor::EBool_(false),
    Expr::expr::ctor::ENat_(100),
    Expr::expr::ctor::ENat_(200)
  );
  auto r7 = e7->eval(Ty::ty::ctor::TNat_());
  ASSERT(std::any_cast<unsigned int>(r7) == 200);
  std::cout << "Test 7 passed: if false then 100 else 200 = 200\n";

  // Test 8: Complex expression combining multiple operations
  // eval (EIf TNat (EEq (EAdd (ENat 2) (ENat 3)) (ENat 5)) (ENat 42) (ENat 0)) = 42
  auto e8 = Expr::expr::ctor::EIf_(
    Ty::ty::ctor::TNat_(),
    Expr::expr::ctor::EEq_(
      Expr::expr::ctor::EAdd_(
        Expr::expr::ctor::ENat_(2),
        Expr::expr::ctor::ENat_(3)
      ),
      Expr::expr::ctor::ENat_(5)
    ),
    Expr::expr::ctor::ENat_(42),
    Expr::expr::ctor::ENat_(0)
  );
  auto r8 = e8->eval(Ty::ty::ctor::TNat_());
  ASSERT(std::any_cast<unsigned int>(r8) == 42);
  std::cout << "Test 8 passed: if (2 + 3 == 5) then 42 else 0 = 42\n";

  // Test 9: Nested conditionals
  // eval (EIf TBool (EBool true) (EBool false) (EBool true)) = false
  auto e9 = Expr::expr::ctor::EIf_(
    Ty::ty::ctor::TBool_(),
    Expr::expr::ctor::EBool_(true),
    Expr::expr::ctor::EBool_(false),
    Expr::expr::ctor::EBool_(true)
  );
  auto r9 = e9->eval(Ty::ty::ctor::TBool_());
  ASSERT(std::any_cast<bool>(r9) == false);
  std::cout << "Test 9 passed: if true then false else true = false\n";

  if (testStatus == 0) {
    std::cout << "\nAll eval_expr tests passed!\n";
  } else {
    std::cout << "\n" << testStatus << " test(s) failed!\n";
  }

  return testStatus;
}

// clang++ -I. -I~/crane/theories/cpp -std=c++23 -c eval_expr.cpp -o eval_expr.o
// clang++ -I. -I~/crane/theories/cpp -std=c++23 -O2 eval_expr.o eval_expr.t.cpp -o eval_expr.t.o; ./eval_expr.t.o
