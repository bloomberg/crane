#include <higher_kinded.h>

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

__attribute__((pure)) unsigned int HigherKinded::tree_sum(
    const std::shared_ptr<HigherKinded::Tree<unsigned int>> &t) {
  return tree_fold<unsigned int, unsigned int>(
      [](unsigned int x) { return x; },
      [](unsigned int _x0, unsigned int _x1) -> unsigned int {
        return (_x0 + _x1);
      },
      t);
}
