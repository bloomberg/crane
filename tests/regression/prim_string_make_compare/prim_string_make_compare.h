#pragma once

#include <crane_string.h>
#include <cstdint>
#include <string>
#include <string_view>
#include <utility>

enum class Comparison;
enum class Comparison { EQ, LT, GT };

struct PrimStringMakeCompare {
  static inline const std::string nuls =
      crane::string_make(INT64_C(3), INT64_C(0));
  static inline const bool nul_length =
      static_cast<int64_t>(nuls.size()) == INT64_C(3);
  static inline const bool cmp_lt = []() {
    switch (static_cast<Comparison>(crane::string_compare(
                std::string_view("ab"), std::string_view("b")))) {
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
      crane::string_max_length == INT64_C(16777211);
  static inline const bool make_clamped = []() {
    std::string s = crane::string_make(
        static_cast<int64_t>((static_cast<uint64_t>(crane::string_max_length) +
                              static_cast<uint64_t>(INT64_C(5))) &
                             0x7FFFFFFFFFFFFFFFULL),
        INT64_C(300));
    return (static_cast<int64_t>(s.size()) == crane::string_max_length &&
            crane::string_get(s, INT64_C(7)) == INT64_C(44));
  }();
  /// compare reads bytes unsigned: a byte of 200 is above "a"; a proper
  /// prefix is below; equal strings are Eq.
  static inline const bool cmp_high_gt = []() {
    switch (static_cast<Comparison>(crane::string_compare(
                crane::string_make(INT64_C(1), INT64_C(200)),
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
    switch (static_cast<Comparison>(crane::string_compare(
                std::string_view("abc"), std::string_view("ab")))) {
    case Comparison::GT: {
      switch (static_cast<Comparison>(crane::string_compare(
                  std::string_view("ab"), std::string_view("ab")))) {
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
