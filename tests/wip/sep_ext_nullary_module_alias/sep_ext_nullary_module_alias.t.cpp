#include "SepExtNullaryModuleAlias.h"

#include <cassert>

struct MyVal {
  using t = unsigned int;
  static constexpr unsigned int empty() { return 0; }
};

struct MyCfg {
  using V = MyVal;
  static constexpr unsigned int default_val() { return 99; }
};

int main() {
  using W = SepExtNullaryModuleAlias::Worker<MyCfg>;
  assert(W::get_empty() == 0);
  assert(W::get_default() == 99);
  return 0;
}
