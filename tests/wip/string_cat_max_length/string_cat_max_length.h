#pragma once

#include <crane_string.h>
#include <cstdint>
#include <string>
#include <string_view>

struct StringCatMaxLength {
  static std::string double_(uint64_t n, std::string s);
  static inline const std::string big = double_(UINT64_C(24), "a");
  static inline const std::string joined = std::string("xyz") + big;
  static inline const bool clamped =
      static_cast<int64_t>(joined.size()) == crane::string_max_length;
  static inline const bool big_clamped =
      static_cast<int64_t>(big.size()) == crane::string_max_length;
};
