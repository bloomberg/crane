#include "SepExtQualifiedRaw.h"

#include <cassert>

struct IntOrd {
  using t = int;
};

int main() {
  using M = SepExtQualifiedRaw::Make<IntOrd>;
  using FMap = M::fmap<double>;

  auto empty = FMap::empty();
  assert(M::is_empty(empty) == true);

  auto n = FMap::node(1, 3.14, FMap::empty());
  assert(M::is_empty(n) == false);

  // Test converting copy constructor (fmap<double> -> fmap<float>)
  using FMapF = M::fmap<float>;
  FMapF converted(n);
  assert(M::is_empty(converted) == false);

  return 0;
}
