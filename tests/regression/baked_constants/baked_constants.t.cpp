#include <baked_constants.h>

#include <cassert>
#include <iostream>

using B = BakedConstants;

int main() {
  // The DAG: 65535 nodes walked, 16 distinct, the children of each one block.
  assert(B::big_size() == 65535);
  const auto &root = crane::get<1>(B::big.v());
  assert(root.l->v().same_as(root.r->v()));
  // Read back immortal: no count is ever written.
  assert(B::big.v().use_count() == ~std::size_t{0});
  // The table: rows from static blocks, the two equal rows one block.
  assert(B::cell(0, 9) == 9 && B::cell(1, 9) == 27 && B::cell(2, 4) == 12 && B::cell(3, 0) == 0);
  assert(B::table.first[1].begin() == B::table.first[2].begin());
  assert(B::accept(0) && !B::accept(1) && B::accept(2) && !B::accept(3));
  // The records: strings and options.
  assert(B::names() == "first");
  assert(B::weights() == 7);
  std::cout << "baked_constants: ok" << std::endl;
  return 0;
}
