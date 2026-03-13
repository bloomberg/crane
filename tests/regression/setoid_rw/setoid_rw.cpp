#include <setoid_rw.h>

#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

__attribute__((pure)) unsigned int SetoidRw::mod3(const unsigned int n) {
  return (n % 3u);
}

__attribute__((pure)) unsigned int
SetoidRw::classify_mod3(const unsigned int n) {
  if (mod3(n) <= 0) {
    return 0u;
  } else {
    unsigned int n0 = mod3(n) - 1;
    if (n0 <= 0) {
      return 1u;
    } else {
      unsigned int _x = n0 - 1;
      return 2u;
    }
  }
}

__attribute__((pure)) unsigned int SetoidRw::add_mod3(const unsigned int x,
                                                      const unsigned int y) {
  return mod3((x + y));
}
