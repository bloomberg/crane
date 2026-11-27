#pragma once

#include <cstdint>

struct Int63ZeroDiv {
  static inline const int64_t d =
      (INT64_C(0) == 0 ? 0 : INT64_C(7) / (INT64_C(0) | (INT64_C(0) == 0)));
  static inline const int64_t m =
      (INT64_C(0) == 0 ? INT64_C(7)
                       : INT64_C(7) % (INT64_C(0) | (INT64_C(0) == 0)));
  static inline const int64_t s =
      (INT64_C(70) >= 63
           ? 0
           : static_cast<int64_t>((UINT64_C(1) << (INT64_C(70) & 63)) &
                                  UINT64_C(9223372036854775807)));
  static inline const int64_t run =
      static_cast<int64_t>(
          (static_cast<uint64_t>(static_cast<int64_t>(
               (static_cast<uint64_t>(d) + static_cast<uint64_t>(m)) &
               UINT64_C(9223372036854775807))) +
           static_cast<uint64_t>(s)) &
          UINT64_C(9223372036854775807));
};
