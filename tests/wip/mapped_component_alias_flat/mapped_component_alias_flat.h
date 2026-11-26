#pragma once

#include "fn.h"
#include <cstdint>
#include <optional>
#include <utility>

struct MappedComponentAliasFlat {
  template <typename a> using st = crane::fn<std::pair<a, uint64_t>(uint64_t)>;

  template <typename T1> static st<T1> sret(T1 a) {
    return [=, a = std::move(a)](uint64_t s) { return std::make_pair(a, s); };
  }

  static inline const uint64_t result =
      [](const auto &_m, auto _d) { return _m.has_value() ? *_m : _d; }(
          std::optional<
              crane::fn<std::pair<uint64_t, uint64_t>(uint64_t, uint64_t)>>{},
          crane::fn<st<uint64_t>(uint64_t)>(sret<uint64_t>))(UINT64_C(4))(
          UINT64_C(5))
                                                                           .first;
};
