// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <module_alias_shadows_global.h>
#include <cassert>

int main() {
  assert(::dbl(5) == 10);
  assert(::seven == 7);
  assert(ModuleAliasShadowsGlobal::R::dbl(5) == 10);
  assert(ModuleAliasShadowsGlobal::R::seven == 7);
  assert(ModuleAliasShadowsGlobal::dbl(5) == 10);
  assert(ModuleAliasShadowsGlobal::seven == 7);
  assert(ModuleAliasShadowsGlobal::even(4));
  assert(!ModuleAliasShadowsGlobal::even(7));
  assert(ModuleAliasShadowsGlobal::t == 14);
  assert(ModuleAliasShadowsGlobal::Q::dbl(3) == 12);
  assert(ModuleAliasShadowsGlobal::Q::seven == 8);
  assert(ModuleAliasShadowsGlobal::Q::u == 32);
  assert(ModuleAliasShadowsGlobal::F3::dbl(4) == 8);
  assert(ModuleAliasShadowsGlobal::F3::seven() == 7);
  assert(ModuleAliasShadowsGlobal::F3::r() == 20);
  return 0;
}
