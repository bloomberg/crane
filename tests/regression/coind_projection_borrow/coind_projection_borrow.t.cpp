// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include "coind_projection_borrow.h"

#include <iostream>
#include <type_traits>
#include <utility>

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

using Stream = CoindProjectionBorrow::Stream::stream;

// An lvalue receiver lends a reference into itself; a temporary one hands out
// a copy, which outlives the full expression that produced the receiver.
static_assert(
    std::is_same_v<decltype(std::declval<const Stream &>().hd()), const uint64_t &>);
static_assert(std::is_same_v<decltype(std::declval<Stream>().hd()), uint64_t>);
static_assert(
    std::is_same_v<decltype(std::declval<const Stream &>().tl()), const Stream &>);
static_assert(std::is_same_v<decltype(std::declval<Stream>().tl()), Stream>);

// n, n + 1, n + 2, ...
static Stream nats_from(uint64_t n) {
  return Stream::lazy_(
      [=]() -> Stream::Scons { return {n, nats_from(n + 1)}; });
}

int main() {
  Stream s = nats_from(10);
  ASSERT(CoindProjectionBorrow::sum_two(s) == 21);
  ASSERT(CoindProjectionBorrow::third(s) == 12);
  ASSERT(CoindProjectionBorrow::third(nats_from(0)) == 2);

  // The reference an lvalue lends stays valid while the receiver lives.
  const uint64_t &head = s.hd();
  const Stream &rest = s.tl();
  ASSERT(head == 10);
  ASSERT(rest.hd() == 11);

  // A temporary's projection is a value of its own.
  uint64_t copied = CoindProjectionBorrow::skip2(nats_from(3)).hd();
  ASSERT(copied == 5);

  if (testStatus == 0) {
    std::cout << "All coind_projection_borrow tests passed!" << std::endl;
  }
  return testStatus;
}
