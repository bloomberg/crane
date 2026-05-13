#include "SepExtConceptInclude.h"

#include <cassert>

struct MyBase {
  using t = int;
  static constexpr int default_() { return 42; }
};
static_assert(SepExtConceptInclude::BaseType<MyBase>);
static_assert(SepExtConceptInclude::DerivedType<MyBase>);

int main() {
  using Use = SepExtConceptInclude::Use<MyBase>;
  assert(Use::get_default() == 42);
  return 0;
}
