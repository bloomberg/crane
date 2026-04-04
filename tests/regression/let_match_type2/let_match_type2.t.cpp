#include <let_match_type2.h>

int main() {
  // Test 1
  auto r1 = LetMatchType2::let_match_bool(0);

  // Test 2
  auto r2 = LetMatchType2::let_match_pair(true);

  // Test 5
  auto r5 = LetMatchType2::cascading_nat(true, false, true);

  // Test 7
  auto r7 = LetMatchType2::match_of_match(3);

  // Test 8
  auto r8 = LetMatchType2::let_match_bindings(5);

  return 0;
}
