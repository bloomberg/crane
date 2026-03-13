#include <keyword_class_global.h>

#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

__attribute__((pure)) unsigned int
KeywordClassGlobal::class_(const unsigned int n) {
  return (n + n);
}
