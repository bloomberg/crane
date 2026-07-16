// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <higher_order.h>

#include <functional>
#include <iostream>
#include <memory>
#include <string>
#include <variant>

namespace {

int testStatus = 0;

struct UnaryU64 {
  uint64_t operator()(uint64_t) const;
};

struct BinaryU64 {
  uint64_t operator()(uint64_t, uint64_t) const;
};

template <typename G, typename F>
concept CanComposeU64 = requires(G &&g, F &&f, uint64_t x) {
  HigherOrder::compose<uint64_t, uint64_t, uint64_t>(std::forward<G>(g),
                                                     std::forward<F>(f), x);
};

static_assert(CanComposeU64<UnaryU64, UnaryU64>);
static_assert(!CanComposeU64<BinaryU64, UnaryU64>);
static_assert(!CanComposeU64<UnaryU64, BinaryU64>);

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
  // Test map: (1+1) + (2+1) + (3+1) + (4+1) + (5+1) = 2+3+4+5+6 = 20
  ASSERT(HigherOrder::test_map == 20u);

  // Test foldr: 1+2+3+4+5 = 15
  ASSERT(HigherOrder::test_foldr == 15u);

  // Test foldl: same as foldr for addition
  ASSERT(HigherOrder::test_foldl == 15u);

  // Test compose: (3+1)*2 = 8
  ASSERT(HigherOrder::test_compose == 8u);

  // Test iterate: 0 + 2 + 2 + 2 = 6
  ASSERT(HigherOrder::test_iterate == 6u);

  // Test adder: 5 + 3 = 8
  ASSERT(HigherOrder::test_adder == 8u);

  // Test twice: (5+1)+1 = 7
  ASSERT(HigherOrder::test_twice == 7u);

  // Test pipe: 5 + 3 = 8
  ASSERT(HigherOrder::test_pipe == 8u);

  return testStatus;
}
