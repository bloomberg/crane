#pragma once

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <string>
#include <string_view>
#include <utility>

enum class Comparison;
enum class Comparison { EQ, LT, GT };

struct PrimStringMakeCompare {
  static inline const std::string nuls = std::string(
      static_cast<std::size_t>(std::min<int64_t>(INT64_C(3), 16777211)),
      static_cast<char>(INT64_C(0)));
  static inline const bool nul_length =
      static_cast<int64_t>(nuls.size()) == INT64_C(3);
  static inline const bool cmp_lt = []() {
    switch (static_cast<Comparison>(
                (std::string_view("ab") < std::string_view("b")) +
                2 * (std::string_view("ab") > std::string_view("b")))) {
    case Comparison::LT: {
      return true;
    }
    default: {
      return false;
    }
    }
  }();
  /// make clamps its length to max_length and its character to the
  /// low byte: make (max_length + 5) 300 is max_length bytes of 44.
  static inline const bool max_length_value =
      INT64_C(16777211) == INT64_C(16777211);
  static inline const bool make_clamped = []() {
    std::string s = std::string(static_cast<std::size_t>(
        std::min<int64_t>(static_cast<int64_t>(
            (static_cast<uint64_t>(INT64_C(16777211)) + UINT64_C(5)) &
            UINT64_C(9223372036854775807)),
                          16777211)),
                                static_cast<char>(INT64_C(300)));
    return ((static_cast<int64_t>(s.size()) == INT64_C(16777211)) &&
            (static_cast<int64_t>(
                 7uz < s.size() ? static_cast<unsigned char>(s[7uz]) : 0) ==
             INT64_C(44)));
  }();
  /// compare reads bytes unsigned: a byte of 200 is above "a"; a proper
  /// prefix is below; equal strings are Eq.
  static inline const bool cmp_high_gt = []() {
    switch (static_cast<Comparison>(
                (std::string(static_cast<std::size_t>(
                     std::min<int64_t>(INT64_C(1), 16777211)),
                             static_cast<char>(INT64_C(200))) <
                 std::string_view("a")) +
                2 * (std::string(static_cast<std::size_t>(
                         std::min<int64_t>(INT64_C(1), 16777211)),
                                 static_cast<char>(INT64_C(200))) >
                     std::string_view("a")))) {
    case Comparison::GT: {
      return true;
    }
    default: {
      return false;
    }
    }
  }();
  static inline const bool cmp_prefix = []() {
    switch (static_cast<Comparison>(
                (std::string_view("abc") < std::string_view("ab")) +
                2 * (std::string_view("abc") > std::string_view("ab")))) {
    case Comparison::GT: {
      switch (static_cast<Comparison>(
                  (std::string_view("ab") < std::string_view("ab")) +
                  2 * (std::string_view("ab") > std::string_view("ab")))) {
      case Comparison::EQ: {
        return true;
      }
      default: {
        return false;
      }
      }
      break;
    }
    default: {
      return false;
    }
    }
  }();
};
