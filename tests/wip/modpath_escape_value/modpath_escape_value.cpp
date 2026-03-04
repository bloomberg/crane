#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <modpath_escape_value.h>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

unsigned int ModpathEscapeValue::A::Value'::f(const unsigned int n){return std::move(n);}

    unsigned int
    ModpathEscapeValue::B::Value_::g(const unsigned int n) {
  return (std::move(n) + 1);
}
