#ifndef INCLUDED_PROJECTION_RESULT_OVERAPPLIED
#define INCLUDED_PROJECTION_RESULT_OVERAPPLIED

#include "fn.h"
#include <cstdint>
#include <utility>

struct Nat {};

struct ProjectionResultOverapplied {
  static inline const std::pair<crane::fn<uint64_t(uint64_t, uint64_t)>,
                                uint64_t>
      fp = std::make_pair(
          [](uint64_t _x0, uint64_t _x1) -> uint64_t { return (_x0 + _x1); },
          UINT64_C(0));
  static inline const uint64_t direct = fp.first(UINT64_C(2))(UINT64_C(3));
  static uint64_t
  getf(const std::pair<crane::fn<uint64_t(uint64_t, uint64_t)>, uint64_t> &x0_,
       uint64_t x1_, uint64_t x2_);
  static inline const uint64_t through_definition =
      getf(fp, UINT64_C(2), UINT64_C(3));
  static uint64_t apply_snd(
      const std::pair<uint64_t, crane::fn<uint64_t(uint64_t, uint64_t)>> &p);
  static inline const uint64_t second = apply_snd(
      std::make_pair(UINT64_C(4), [](uint64_t _x0, uint64_t _x1) -> uint64_t {
        return (_x0 * _x1);
      }));
};

#endif // INCLUDED_PROJECTION_RESULT_OVERAPPLIED
