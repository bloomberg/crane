#pragma once

#include "fn.h"
#include <cstdint>
#include <memory>
#include <optional>
#include <utility>

struct PolyInstanceCurriedFn {
  template <typename T1> static std::optional<T1> id2(std::optional<T1> o) {
    return o;
  }

  static inline const std::optional<crane::fn<uint64_t(bool,
                                                       uint64_t)>> none_const =
      id2<crane::fn<uint64_t(bool, uint64_t)>>(
          std::optional<crane::fn<uint64_t(bool, uint64_t)>>());
  static std::optional<crane::fn<uint64_t(bool, uint64_t)>> none_fn(bool _x);
  static uint64_t
  use_result(std::optional<crane::fn<uint64_t(bool, uint64_t)>> o);
  static std::optional<crane::fn<uint64_t(bool, uint64_t)>>
  pass(std::optional<crane::fn<uint64_t(bool, uint64_t)>> x0_);
  static inline const uint64_t result = []() -> uint64_t {
    if (none_const.has_value()) {
      const crane::fn<uint64_t(bool, uint64_t)> &_x = *none_const;
      return UINT64_C(0);
    } else {
      auto _cs = none_fn(true);
      if (_cs.has_value()) {
        const crane::fn<uint64_t(bool, uint64_t)> &_x = *_cs;
        return UINT64_C(0);
      } else {
        return UINT64_C(1);
      }
    }
  }() +
   use_result(pass(std::make_optional<crane::fn<uint64_t(bool, uint64_t)>>(
       crane::fn<uint64_t(bool, uint64_t)>([](bool b, uint64_t n) -> uint64_t {
         if (b) {
           return n + UINT64_C(2);
         } else {
           return UINT64_C(0);
         }
       }))));
};
