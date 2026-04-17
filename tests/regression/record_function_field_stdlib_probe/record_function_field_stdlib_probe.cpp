#include <record_function_field_stdlib_probe.h>

#include <functional>
#include <memory>
#include <type_traits>
#include <utility>

__attribute__((pure)) Bool0 Datatypes::negb(const Bool0 b) {
  switch (b) {
  case Bool0::e_TRUE0: {
    return Bool0::e_FALSE0;
  }
  case Bool0::e_FALSE0: {
    return Bool0::e_TRUE0;
  }
  default:
    std::unreachable();
  }
}
