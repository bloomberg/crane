#include <closure_chain.h>

#include <cassert>
#include <iostream>

int main() {
  using CC = ClosureChain;

  // chain_0: make_chain 0 t 5 = tree_sum(t) + 5 = 10 + 5 = 15
  auto r0 = CC::chain_0;
  std::cout << "chain_0 = " << r0 << std::endl;
  assert(r0 == 15u);

  // chain_1: make_chain 1 t 5 = (make_chain 0 t) (5+1) = 10 + 6 = 16
  auto r1 = CC::chain_1;
  std::cout << "chain_1 = " << r1 << std::endl;
  assert(r1 == 16u);

  // chain_3: make_chain 3 t 0 = 10 + 3 = 13
  auto r3 = CC::chain_3;
  std::cout << "chain_3 = " << r3 << std::endl;
  assert(r3 == 13u);

  // chain_double_call: f = make_chain 2 t, called twice
  // BUG: [&] capture with std::move(t) inside lambda. First call
  // converts unique_ptr to shared_ptr (consuming it), second call
  // passes null → count_nodes dereferences null → CRASH
  // Expected: make_chain(2,t,0) + make_chain(2,t,100) = 12 + 112 = 124
  auto r4 = CC::chain_double_call;
  std::cout << "chain_double_call = " << r4 << std::endl;
  assert(r4 == 124u);

  std::cout << "All closure_chain tests passed!" << std::endl;
  return 0;
}
