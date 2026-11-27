#pragma once

#include "crane_fn.h"
#include "fn.h"
#include "obj.h"
#include "shared_block.h"
#include <cstdint>
#include <type_traits>
#include <utility>

struct Datatypes {
  static crane::obj id(crane::obj x);
};

struct IdAnyCastFlatFn {
  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, T1> &&
             std::is_invocable_r_v<T1, F0 &, const T1 &>
  static T1 twice(F0 &&f, const T1 &x) {
    return f(f(x));
  }

  static inline const uint64_t result = []() {
    return twice<crane::fn<uint64_t(uint64_t)>>(
        []() {
          // Built on the first call and immortal: every thread reads it without
          // touching its counts.
          static const auto erased_fn = crane::immortal(
              crane_erase_fn([](const crane::fn<uint64_t(uint64_t)> &c,
                                uint64_t n) { return (c(n) + UINT64_C(1)); }));
          crane::fn<uint64_t(crane::fn<uint64_t(uint64_t)>, uint64_t)> _rg =
              crane_any_cast<
                  crane::fn<uint64_t(crane::fn<uint64_t(uint64_t)>, uint64_t)>>(
                  Datatypes::id(erased_fn));
          return [=, _rg = std::move(_rg)](crane::fn<uint64_t(uint64_t)> _rg0_0) {
            return [=, _rg = _rg](uint64_t _rg1_0) {
              return _rg(_rg0_0, _rg1_0);
            };
          };
        }(),
        [](uint64_t n) { return n; })(UINT64_C(0));
  }();
};
