#pragma once

#include "obj.h"
#include <concepts>

namespace ProvDef {
using prov = crane::obj;
template <typename I>
concept Provenance = requires {
  typename I::prov;
} && (requires {
  {
    I::nil_prov()
  }
  -> std::convertible_to<typename I::prov>;
} || requires {
  {
    I::nil_prov
  }
  -> std::convertible_to<typename I::prov>;
});
} // namespace ProvDef
