#ifndef INCLUDED_RECORD_APPLY
#define INCLUDED_RECORD_APPLY

#include <functional>

struct RecordApply {
  struct R {
    std::function<uint64_t(uint64_t, uint64_t)> f;
    uint64_t _tag;

    // ACCESSORS
    R clone() const { return R{this->f, this->_tag}; }
  };

  static uint64_t apply_record(const R &r0, uint64_t a, uint64_t b);
  static inline const R r =
      R{[](uint64_t x, uint64_t) { return x; }, UINT64_C(3)};
  static inline const uint64_t three = r.f(UINT64_C(3), UINT64_C(0));
};

#endif // INCLUDED_RECORD_APPLY
