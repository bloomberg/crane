#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <reg_pair_even_projection.h>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

unsigned int RegPairEvenProjection::pair_base(const unsigned int r) {
  return (((r - (r % ((0 + 1) + 1))) > r ? 0 : (r - (r % ((0 + 1) + 1)))));
}
