#include <nested_statet_ret_type.h>

#include <cassert>
#include <iostream>

static int nat_to_int(const Nat &n) {
  int c = 0;
  Nat m = n;
  while (std::holds_alternative<typename Nat::S>(m.v())) {
    c++;
    m = *std::get<typename Nat::S>(m.v()).a0;
  }
  return c;
}

int main() {
  // stacked 4 true = Ret (false, (5, 4)).
  assert(nat_to_int(NestedStatetRetType::unstacked) == 5);
  std::cout << "nested_statet_ret_type: ok" << std::endl;
  return 0;
}
