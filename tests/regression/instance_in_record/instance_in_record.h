#ifndef INCLUDED_INSTANCE_IN_RECORD
#define INCLUDED_INSTANCE_IN_RECORD

#include "crane_fn.h"
#include "fn.h"
#include "obj.h"
#include <cstdint>
#include <stdexcept>

struct InstanceInRecord {
  template <typename A> struct Monoid {
    A unit_;
    crane::fn<A(A, A)> op;

    // ACCESSORS
    template <typename CraneU> operator Monoid<CraneU>() const {
      return {[&]() -> CraneU {
                if constexpr (crane_convertible<CraneU, const A &>) {
                  return crane_convert<CraneU>(unit_);
                } else {
                  throw std::logic_error("unreachable: inactive constructor "
                                         "field at this instantiation");
                }
              }(),
              crane_convert<crane::fn<CraneU(CraneU, CraneU)>>(op)};
    }
  };

  static inline const Monoid<uint64_t> MNat =
      Monoid<uint64_t>{UINT64_C(0), [](uint64_t _x0, uint64_t _x1) -> uint64_t {
                         return (_x0 + _x1);
                       }};

  struct bundle {
    Monoid<uint64_t> carrierDict;
    uint64_t seed;
  };

  static inline const bundle b = bundle{MNat, UINT64_C(5)};
  static inline const uint64_t run =
      b.carrierDict.op(b.seed, b.carrierDict.unit_);
};

#endif // INCLUDED_INSTANCE_IN_RECORD
