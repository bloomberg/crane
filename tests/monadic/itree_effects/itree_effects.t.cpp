// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.

// Test: Effect composition using the real InteractionTrees library.
//
// Verifies that two effect types (consoleE +' logE) compose correctly
// and the ITree infrastructure is fully erased in generated C++.

#include <itree_effects.h>

#include <cassert>
#include <iostream>

void test_simple_log() {
  // simple_log just does (void)0 comments — no visible output
  ITreeEffects::simple_log();
  std::cout << "PASS: test_simple_log" << std::endl;
}

void test_simple_print() {
  // simple_print outputs two lines to stdout
  ITreeEffects::simple_print();
  std::cout << "PASS: test_simple_print" << std::endl;
}

void test_pure_value() {
  // pure_value returns Nat 42 — verify it's 42 S constructors
  auto n = ITreeEffects::pure_value();
  unsigned int count = 0;
  while (std::holds_alternative<Nat::S>(n->v())) {
    count++;
    n = std::get<Nat::S>(n->v()).d_a0;
  }
  assert(count == 42);
  std::cout << "PASS: test_pure_value" << std::endl;
}

int main() {
  test_simple_log();
  test_simple_print();
  test_pure_value();

  std::cout << "All itree_effects tests passed!" << std::endl;
  return 0;
}
