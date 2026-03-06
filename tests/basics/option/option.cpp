#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <option.h>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

unsigned int Option::get_or_default(const std::optional<unsigned int> o,
                                    const unsigned int default0) {
  if (o.has_value()) {
    unsigned int x = *o;
    return std::move(x);
  } else {
    return std::move(default0);
  }
}

std::optional<unsigned int> Option::safe_pred(const unsigned int n) {
  if (n <= 0) {
    return std::nullopt;
  } else {
    unsigned int m = n - 1;
    return std::make_optional<unsigned int>(m);
  }
}

std::optional<unsigned int>
Option::chain_options(const std::optional<unsigned int> o1,
                      const std::optional<unsigned int> o2) {
  if (o1.has_value()) {
    unsigned int _x = *o1;
    return o1;
  } else {
    return std::move(o2);
  }
}
