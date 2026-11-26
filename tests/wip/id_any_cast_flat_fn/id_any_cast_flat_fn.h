#pragma once

#include "crane_fn.h"
#include "fn.h"
#include "obj.h"
#include <cstdint>
#include <type_traits>

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

  static inline const uint64_t result = twice<crane::fn<uint64_t(uint64_t)>>(
      crane::any_cast<
          crane::fn<uint64_t(crane::fn<uint64_t(uint64_t)>, uint64_t)>>(
          Datatypes::id(
              crane_erase_fn([](const crane::fn<uint64_t(uint64_t)> &c,
                                uint64_t n) { return (c(n) + UINT64_C(1)); }))),
      [](uint64_t n) { return n; })(UINT64_C(0));
};
