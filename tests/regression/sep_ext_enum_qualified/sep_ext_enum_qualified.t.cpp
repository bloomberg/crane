#include "SepExtEnumQualified.h"

#include <cassert>

struct IntOrd {
  using t = int;
  static Datatypes::Comparison compare(int a, int b) {
    if (a < b) return Datatypes::Comparison::LT;
    if (a == b) return Datatypes::Comparison::EQ;
    return Datatypes::Comparison::GT;
  }
};

int main() {
  using M = SepExtEnumQualified::Make<IntOrd>;

  assert(M::is_lt(1, 2) == true);
  assert(M::is_lt(2, 1) == false);
  assert(M::is_lt(1, 1) == false);

  assert(M::is_eq(1, 1) == true);
  assert(M::is_eq(1, 2) == false);

  return 0;
}
