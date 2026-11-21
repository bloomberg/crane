#pragma once

#include <cstdint>
#include <persistent_array.h>
#include <stdexcept>

struct PrimArray {
  template <typename T1> static T1 default0(const persistent_array<T1> &x0_);
};

struct PrimArrayDefault {
  static inline const persistent_array<uint64_t> arr =
      persistent_array<uint64_t>(INT64_C(2), UINT64_C(7));
  static inline const uint64_t dflt =
      PrimArray::template default0<uint64_t>(arr);
};

template <typename T1> T1 PrimArray::default0(const persistent_array<T1> &) {
  throw std::logic_error("unrealized axiom: Corelib.Array.PrimArray.default");
}
