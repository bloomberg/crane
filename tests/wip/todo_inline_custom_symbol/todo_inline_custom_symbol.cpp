#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <todo_inline_custom_symbol.h>
#include <todo_inline_custom_symbol_support.h>
#include <variant>

unsigned int TodoInlineCustomSymbol::alias(const unsigned int _x0) {
  return inline_inc_impl;
}

unsigned int TodoInlineCustomSymbol::twice(const unsigned int n) {
  return alias(alias(n));
}
