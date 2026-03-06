#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <ram_addr_disjoint_bool.h>
#include <stdexcept>
#include <string>
#include <variant>

bool RamAddrDisjointBool::ram_addr_disjointb(
    const unsigned int b1, const unsigned int c1, const unsigned int r1,
    const unsigned int i1, const unsigned int b2, const unsigned int c2,
    const unsigned int r2, const unsigned int i2) {
  return !(((((b1 == b2) && (c1 == c2)) && (r1 == r2)) && (i1 == i2)));
}
