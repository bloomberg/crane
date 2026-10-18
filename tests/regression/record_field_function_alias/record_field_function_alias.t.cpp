#include <cassert>
#include <record_field_function_alias.h>

int main() {
  using M = RecordFieldFunctionAlias;
  assert(M::t1);
  assert(M::t2);
  assert(!M::t3);
  return 0;
}
