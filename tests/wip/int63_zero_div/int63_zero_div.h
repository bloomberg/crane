#ifndef INCLUDED_INT63_ZERO_DIV
#define INCLUDED_INT63_ZERO_DIV

#include <cstdint>

struct Int63ZeroDiv {
  static inline const int64_t d =
      (INT64_C(0) == 0 ? 0 : INT64_C(7) / INT64_C(0));
  static inline const int64_t m =
      (INT64_C(0) == 0 ? 0 : INT64_C(7) % INT64_C(0));
  static inline const int64_t s =
      (INT64_C(70) >= 63
           ? 0
           : static_cast<int64_t>(
                 (static_cast<uint64_t>(INT64_C(1)) << INT64_C(70)) &
                 0x7FFFFFFFFFFFFFFFULL));
  static inline const int64_t run = static_cast<int64_t>(
      (static_cast<uint64_t>(static_cast<int64_t>(
           (static_cast<uint64_t>(d) + static_cast<uint64_t>(m)) &
           0x7FFFFFFFFFFFFFFFULL)) +
       static_cast<uint64_t>(s)) &
      0x7FFFFFFFFFFFFFFFULL);
};

#endif // INCLUDED_INT63_ZERO_DIV
