#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <higher_kinded.h>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

unsigned int HigherKinded::tree_sum(
    const std::shared_ptr<HigherKinded::Tree<unsigned int>> &t) {
  return tree_fold<unsigned int, unsigned int>(
      [](unsigned int x) { return x; },
      [](const unsigned int _x0, const unsigned int _x1) {
        return (_x0 + _x1);
      },
      t);
}
