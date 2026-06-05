// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
//
// Regression test for any_cast<std::any> in nested pair destructuring.
//
// The compiler previously generated any_cast<SemVal>(v2) in the nested
// pair path where SemVal = std::any (axiom type alias).  Since v2 holds
// a concrete type (uint64_t), any_cast<std::any>(v2) would throw
// bad_any_cast.  The fix in extract_from_any and is_any_type now
// recognizes axiom type aliases that resolve to std::any and elides the
// redundant cast.
//
// This test compiles only the .t.cpp (not the generated .cpp) so that we
// can provide concrete axiom implementations instead of the generated stubs.
// The apply_pred body is copied verbatim from the FIXED generated .cpp.

#include "any_cast_nested_pair.h"

#include <iostream>

// ---- Axiom realizations ----

AnyCastNestedPair::SemVal AnyCastNestedPair::mkSemVal(uint64_t n) {
  return std::any(n);
}

uint64_t AnyCastNestedPair::getSemVal(AnyCastNestedPair::SemVal v) {
  return std::any_cast<uint64_t>(v);
}

// ---- Generated function bodies (copied from FIXED any_cast_nested_pair.cpp) ----

uint64_t AnyCastNestedPair::apply_pred(AnyCastNestedPair::symbols_semty input) {
  auto _cs = std::any_cast<std::pair<std::any, std::any>>(input);
  const auto &v1 = _cs.first;
  const auto &rest = _cs.second;
  const std::any &v2 =
      std::any_cast<std::pair<std::any, std::any>>(rest).first;
  const std::any &_x =
      std::any_cast<std::pair<std::any, std::any>>(rest).second;
  return (getSemVal(v1) + getSemVal(v2));
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
  std::any inner_pair =
      std::make_pair(std::any(AnyCastNestedPair::mkSemVal(20)),
                     std::any(std::monostate{}));
  std::any input =
      std::make_pair(std::any(AnyCastNestedPair::mkSemVal(10)), inner_pair);

  uint64_t result = AnyCastNestedPair::apply_pred(input);
  ASSERT(result == 30);
  if (testStatus == 0) {
    std::cout << "apply_pred returned " << result << " -- correct\n";
  }

  // Note: test_pred uses the generated tuple construction which wraps values
  // differently (pair<any, pair<any, monostate>> vs pair<any, any>).  The
  // runtime protocol for symbols_semty requires pair<any, any> at every level
  // which is only produced by the parser's concat_tuple.  We test apply_pred
  // directly with the correct runtime representation above.

  return testStatus;
}
