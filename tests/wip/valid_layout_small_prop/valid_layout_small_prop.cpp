#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <valid_layout_small_prop.h>
#include <variant>

unsigned int ValidLayoutSmallProp::base_addr(
    const std::shared_ptr<ValidLayoutSmallProp::layout> &l) {
  return l->base_addr;
}

unsigned int ValidLayoutSmallProp::code_size(
    const std::shared_ptr<ValidLayoutSmallProp::layout> &l) {
  return l->code_size;
}
