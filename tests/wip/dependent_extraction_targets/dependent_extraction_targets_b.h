#ifndef INCLUDED_DEPENDENT_EXTRACTION_TARGETS_B
#define INCLUDED_DEPENDENT_EXTRACTION_TARGETS_B

#include <cstdint>
#include <dependent_extraction_targets_inner.h>
#include <variant>

struct DependentExtractionTargets {
  struct A {
    struct t {
      // DATA
      uint64_t a0;

      // ACCESSORS
      t clone() const { return {a0}; }

      // CREATORS
      static t t0(uint64_t a0) { return {a0}; }
    };

    static uint64_t get(const t &x);
  };

  struct B {
    static inline const uint64_t use = A::get(A::t::t0(UINT64_C(9)));
  };
};

#endif // INCLUDED_DEPENDENT_EXTRACTION_TARGETS_B
