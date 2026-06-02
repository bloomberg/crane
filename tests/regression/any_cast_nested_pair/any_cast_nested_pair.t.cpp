// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
//
// Regression test for any_cast<std::any> in nested pair destructuring.
//
// The generated apply_pred function has an asymmetry:
//   v1 (from outer pair .first):  used directly — outer Fix C (line 7450) skips cast
//   v2 (from inner pair .first):  any_cast<SemVal>(v2) — apply_fixc_to_nested catch-all
//
// Since SemVal = std::any (axiom), this becomes any_cast<std::any>(v2).
// v2 holds a SemVal (= any(uint64_t)) from mkSemVal.  any_cast<std::any>(v2)
// checks typeid == typeid(std::any), but the stored type is uint64_t -> throws.
//
// This test compiles only the .t.cpp (not the generated .cpp) so that we can
// provide concrete axiom implementations instead of the generated stubs.
// The apply_pred body is copied verbatim from the generated .cpp.

#include "any_cast_nested_pair.h"

#include <iostream>

// ---- Axiom realizations ----

AnyCastNestedPair::SemVal AnyCastNestedPair::mkSemVal(uint64_t n) {
  return std::any(n);
}

uint64_t AnyCastNestedPair::getSemVal(AnyCastNestedPair::SemVal v) {
  return std::any_cast<uint64_t>(v);
}

// ---- Generated function bodies (copied from any_cast_nested_pair.cpp) ----
// These are the GENERATED implementations showing the bug.

uint64_t AnyCastNestedPair::apply_pred(AnyCastNestedPair::symbols_semty input) {
  auto _cs = std::any_cast<std::pair<std::any, std::any>>(input);
  const auto &v1 = _cs.first;
  const auto &rest = _cs.second;
  const std::any &v2 =
      std::any_cast<std::pair<std::any, std::any>>(rest).first;
  const std::any &_x =
      std::any_cast<std::pair<std::any, std::any>>(rest).second;
  // BUG: any_cast<SemVal> where SemVal = std::any
  // v2 holds uint64_t (from mkSemVal), not std::any.
  // any_cast<std::any>(v2) throws bad_any_cast.
  return (getSemVal(v1) +
          getSemVal(std::any_cast<AnyCastNestedPair::SemVal>(v2)));
}

uint64_t AnyCastNestedPair::test_pred(uint64_t a, uint64_t b) {
  return apply_pred(std::make_pair(mkSemVal(a),
                                   std::make_pair(mkSemVal(b),
                                                  std::monostate{})));
}

// ---- Test ----

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
  // Construct input as pair<any,any> at every level (matching concat_tuple).
  // Structure: pair<any,any>( mkSemVal(10), pair<any,any>(mkSemVal(20), monostate) )
  std::any inner_pair =
      std::make_pair(std::any(AnyCastNestedPair::mkSemVal(20)),
                     std::any(std::monostate{}));
  std::any input =
      std::make_pair(std::any(AnyCastNestedPair::mkSemVal(10)), inner_pair);

  // Expected: getSemVal(v1) + getSemVal(v2) = 10 + 20 = 30
  //
  // Actual: any_cast<std::any>(v2) throws because v2 holds uint64_t(20),
  // not std::any.  The fix at line 7450 prevents this for v1 (outer path)
  // but apply_fixc_to_nested (inner path) still generates the wrong cast.
  try {
    uint64_t result = AnyCastNestedPair::apply_pred(input);
    ASSERT(result == 30);
    if (testStatus == 0) {
      std::cout << "apply_pred returned " << result << " -- correct\n";
    }
  } catch (const std::bad_any_cast &e) {
    std::cout << "CAUGHT std::bad_any_cast: " << e.what() << "\n";
    std::cout << "Bug confirmed: any_cast<std::any>(v2) in nested pair path\n";
    ++testStatus;
  }

  return testStatus;
}
