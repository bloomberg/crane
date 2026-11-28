#pragma once

#include "obj.h"
#include <cstdint>
#include <memory>
#include <optional>

struct Datatypes {
  static crane::obj id(crane::obj x);
};

struct IdMappedOptionShape {
  static uint64_t fo(std::optional<uint64_t> o);
  static inline const uint64_t m = fo(crane::any_cast<std::optional<uint64_t>>(
      Datatypes::id(std::make_optional<crane::obj>(crane::obj(UINT64_C(4))))));
};
