#pragma once

#include <cstdint>
#include <string>
#include <string_view>

struct StringCatMaxLength {
  static std::string double_(uint64_t n, std::string s);
  static inline const std::string big = double_(UINT64_C(24), "a");
  static inline const std::string joined =
      (std::string("xyz") + big).substr(0, 16777211);
  static inline const bool clamped =
      static_cast<int64_t>(joined.size()) == INT64_C(16777211);
  static inline const bool big_clamped =
      static_cast<int64_t>(big.size()) == INT64_C(16777211);
};
