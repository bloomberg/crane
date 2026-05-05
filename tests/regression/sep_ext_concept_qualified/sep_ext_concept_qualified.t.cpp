#include "SepExtConceptQualified.h"

#include <cassert>

struct IntOrdered {
  using t = int;
  static Datatypes::Comparison compare(int a, int b) {
    if (a < b)
      return Datatypes::Comparison::e_LT;
    if (a == b)
      return Datatypes::Comparison::e_EQ;
    return Datatypes::Comparison::e_GT;
  }
};
static_assert(SepExtConceptQualified::OrderedType<IntOrdered>);

int main() {
  using Make = SepExtConceptQualified::Make<IntOrdered>;
  assert(Make::is_eq(3, 3));
  assert(!Make::is_eq(3, 4));
  return 0;
}
