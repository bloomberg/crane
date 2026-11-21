#pragma once

#include <cstdint>
#include <string>
#include <string_view>

#include "crane_bake.h"
extern const crane::bake::image crane_baked_word_7b0191877a0d;

struct BakeStringLiteral {
  static inline const std::string word =
      crane::bake::read<std::string>(crane_baked_word_7b0191877a0d);
  static inline const bool word_ok =
      static_cast<int64_t>(word.size()) == INT64_C(3);
};
