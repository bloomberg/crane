// A function on a type, from a later file whose name begins with the type's
// (num_le_two in NumDec.v, for num in Num.v): under separate extraction it
// stays a free function in NumDec.h rather than becoming a method in Num.h,
// where it would name NumOps::two, and NumOps.h itself includes Num.h.
#include "Num.h"
#include "NumOps.h"
#include "NumDec.h"
#include "SepExtCrossFileMethod.h"

#include <cassert>

int main() {
  assert(SepExtCrossFileMethod::use_it);
  return 0;
}
