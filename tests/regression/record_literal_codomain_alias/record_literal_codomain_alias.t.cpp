#include <cassert>
#include <record_literal_codomain_alias.h>

int main() {
  using M = RecordLiteralCodomainAlias;
  assert(M::through_parameter);
  assert(M::through_field);
  return 0;
}
