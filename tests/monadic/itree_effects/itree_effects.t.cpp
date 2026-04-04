// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.

// Test: Effect composition using the real InteractionTrees library.
//
// Verifies that three effect types (consoleE +' randomE +' timeE) compose
// correctly and the ITree infrastructure is fully erased in generated C++.

#include <itree_effects.h>

#include <cassert>
#include <iostream>

void test_roll_dice() {
  auto result = ITreeEffects::roll_dice(6);
  assert(result >= 1 && result <= 6);
  std::cout << "PASS: test_roll_dice (rolled " << result << ")" << std::endl;
}

void test_timed_greeting() {
  // Just verify it runs without error
  ITreeEffects::timed_greeting();
  std::cout << "PASS: test_timed_greeting" << std::endl;
}

int main() {
  test_roll_dice();
  test_timed_greeting();
  std::cout << "All itree_effects tests passed!" << std::endl;
  return 0;
}
