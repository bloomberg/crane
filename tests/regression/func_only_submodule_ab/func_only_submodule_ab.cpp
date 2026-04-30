#include <func_only_submodule_ab.h>

unsigned int FuncOnlySubmoduleAb::Root::A::inc(unsigned int n) {
  return (n + 1);
}

unsigned int FuncOnlySubmoduleAb::Root::B::dec(const unsigned int &_x0) {
  return (_x0 ? _x0 - 1 : _x0);
}
