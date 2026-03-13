#include <func_only_submodule_ab.h>

#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

__attribute__((pure)) unsigned int
FuncOnlySubmoduleAb::Root::A::inc(const unsigned int n) {
  return (std::move(n) + 1);
}

__attribute__((pure)) unsigned int
FuncOnlySubmoduleAb::Root::B::dec(const unsigned int _x0) {
  return (_x0 ? _x0 - 1 : _x0);
}
