#include <eponymous_enum_module.h>

#include <cassert>

int main() {
  using E = EponymousEnumModule::eponymousEnumModule;
  assert(EponymousEnumModule::next(E::RED) == E::GREEN);
  assert(EponymousEnumModule::next(E::GREEN) == E::BLUE);
  assert(EponymousEnumModule::next(E::BLUE) == E::RED);
  assert(EponymousEnumModule::is_red(E::RED));
  assert(!EponymousEnumModule::is_red(E::BLUE));
  return 0;
}
