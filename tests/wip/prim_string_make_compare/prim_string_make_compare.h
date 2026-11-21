#pragma once

#include <cstdint>
#include <stdexcept>
#include <string>
#include <string_view>
#include <utility>

enum class Comparison;
enum class Comparison { EQ, LT, GT };

struct PrimString {
  static std::string make(int64_t x0_, char x1_);
  static Comparison compare(const std::string &x0_, const std::string &x1_);
};

struct PrimStringMakeCompare {
  static inline const std::string nuls =
      PrimString::make(INT64_C(3), INT64_C(0));
  static inline const bool nul_length =
      static_cast<int64_t>(nuls.size()) == INT64_C(3);
  static inline const bool cmp_lt = []() {
    switch (PrimString::compare("ab", "b")) {
    case Comparison::LT: {
      return true;
    }
    default: {
      return false;
    }
    }
  }();
};
