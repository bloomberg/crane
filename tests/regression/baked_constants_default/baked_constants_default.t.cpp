#include <baked_constants_default.h>

#include <cassert>
#include <iostream>

using B = BakedConstantsDefault;

int main() {
  // The tree: 65535 nodes walked.  Without SharedVariant each child is a
  // pointer of its own, so the value is a tree, and is read back as one.
  assert(B::big_size() == 65535);
  // The table: rows from static blocks, the two equal rows one block.
  assert(B::cell(0, 9) == 9 && B::cell(1, 9) == 27 && B::cell(2, 4) == 12 && B::cell(3, 0) == 0);
  assert(B::table.first[1].begin() == B::table.first[2].begin());
  assert(B::accept(0) && !B::accept(1) && B::accept(2) && !B::accept(3));
  // The records: strings and options.
  assert(B::names() == "first");
  assert(B::weights() == 7);
  std::cout << "baked_constants_default: ok" << std::endl;
  return 0;
}
