#include <todo_extract_constant_noninline.h>

#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <todo_extract_constant_noninline_support.h>
#include <variant>

__attribute__((pure)) unsigned int
TodoExtractConstantNoninline::foreign_inc(const unsigned int _x0) {
  return foreign_inc_impl(_x0);
}
