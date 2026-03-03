#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <keyword_param_virtual.h>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

unsigned int KeywordParamVirtual::id(const unsigned int virtual0) {
  return std::move(virtual0);
}
