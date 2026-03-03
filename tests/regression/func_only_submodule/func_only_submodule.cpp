#include <algorithm>
#include <any>
#include <cassert>
#include <func_only_submodule.h>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

unsigned int FuncOnlySubmodule::Outer::Inner::bump(const unsigned int n) {
  return (std::move(n) + 1);
}
