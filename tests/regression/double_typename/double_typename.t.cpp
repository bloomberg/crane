#include "double_typename.h"

#include <cassert>

int main() {
  // Test that pattern matching on dependent types emits single typename
  auto result = DoubleTypename::test;
  assert(std::holds_alternative<List<unsigned int>::Cons>(result.v()));
  const auto &[d_a0, d_a1] =
      std::get<List<unsigned int>::Cons>(result.v());
  assert(d_a0 == 1u);

  return 0;
}
