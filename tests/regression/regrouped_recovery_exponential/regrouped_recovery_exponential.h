#pragma once

#include "crane_fn.h"
#include "fn.h"
#include "obj.h"
#include <cstdint>
#include <type_traits>
#include <utility>

struct Datatypes {
  static crane::obj id(crane::obj x);
};

struct RegroupedRecoveryExponential {
  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, T1> &&
             std::is_invocable_r_v<T1, F0 &, const T1 &>
  static T1 twice(F0 &&f, const T1 &x) {
    return f(f(x));
  }

  static uint64_t lvl(uint64_t d);
};
