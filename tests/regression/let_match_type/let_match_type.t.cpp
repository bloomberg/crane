#include <let_match_type.h>

int main() {
  // Test 1: let-bound bool match
  auto r1 = LetMatchType::let_match_nat(true);

  // Test 3: let-bound option match
  auto r3 = LetMatchType::let_match_option(std::make_optional(5u));

  // Test 4: nested bool match
  auto r4 = LetMatchType::let_nested_bool(true, false);

  // Test 5: multiple let-bound matches
  auto r5 = LetMatchType::multi_let_match(true, false);

  // Test 6: let-bound match in arg
  auto r6 = LetMatchType::let_match_in_arg(3);

  return 0;
}
