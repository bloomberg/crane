#ifndef INCLUDED_INSTANCE_IN_RECORD
#define INCLUDED_INSTANCE_IN_RECORD

#include <functional>

struct InstanceInRecord {
  template <typename A> struct Monoid {
    A unit_;
    std::function<A(A, A)> op;
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
