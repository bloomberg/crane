#include "SepExtModuleAbbrev.h"

#include <cassert>

struct IntOrd {
  using t = int;
};

struct IntWS {
  struct E {
    using t = int;
  };
  using key = long;
};

static_assert(SepExtModuleAbbrev::OrderedType<IntOrd>);
static_assert(SepExtModuleAbbrev::WS<IntWS>);

int main() {
  // WFacts inherits from OrdFacts — test that inherited methods are accessible.
  using F = SepExtModuleAbbrev::WFacts<IntWS>;
  assert(F::key_eq(1L, 2L));
  assert(F::ord_eq(3, 4));

  // KeyFacts exposes ME as a type alias for M::E.
  using KF = SepExtModuleAbbrev::KeyFacts<IntWS>;
  static_assert(std::is_same_v<KF::ME, IntWS::E>);

  return 0;
}
