#include <prod_fst_projection.h>
#include <cassert>
#include <iostream>
int main() {
  // `depth` walks the chain via `fst`, whose `%a0.first` template splices the
  // dereferenced `shared_ptr<pair<t, nat>>` field.
  std::cout << "go = " << ProdFstProjection::go(5) << " (want 5)" << std::endl;
  assert(ProdFstProjection::go(5) == 5);
  return 0;
}
