// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <poly_throwing_call.h>
#include <cassert>
#include <stdexcept>

int main() {
  assert(PolyThrowingCall::ok() == 3);
  assert(PolyThrowingCall::flag_ok());
  bool threw = false;
  try {
    PolyThrowingCall::count(2, 5);
  } catch (const std::exception &) {
    threw = true;
  }
  assert(threw);
  return 0;
}
