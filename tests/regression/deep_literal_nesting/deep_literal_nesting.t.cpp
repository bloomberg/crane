#include <deep_literal_nesting.h>
#include <cassert>
#include <iostream>

static unsigned nat_to_uint(const Nat &n) {
  unsigned acc = 0;
  const Nat *cur = &n;
  while (std::holds_alternative<Nat::S>(cur->v())) {
    ++acc;
    cur = std::get<Nat::S>(cur->v()).a0.get();
  }
  return acc;
}

int main() {
  std::cout << nat_to_uint(DeepLiteralNesting::run) << std::endl;
  assert(nat_to_uint(DeepLiteralNesting::run) == 3400);
  return 0;
}
