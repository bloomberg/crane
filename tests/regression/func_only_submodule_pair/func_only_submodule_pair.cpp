#include <algorithm>
#include <any>
#include <cassert>
#include <func_only_submodule_pair.h>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

unsigned int FuncOnlySubmodulePair::Outer::A::inc(const unsigned int n) {
  return (std::move(n) + 1);
}

unsigned int FuncOnlySubmodulePair::Outer::B::dec(const unsigned int _x0) {
  return (_x0 ? _x0 - 1 : _x0);
}
