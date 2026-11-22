#include <bde_concept_declval_include.h>

#include <cassert>
#include <iostream>

int main() {
  auto r = BdeConceptDeclvalInclude::result;
  std::cout << "result = " << r << std::endl;
  assert(r == 8);
  return 0;
}
