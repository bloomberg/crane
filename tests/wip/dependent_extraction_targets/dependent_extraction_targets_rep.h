#ifndef INCLUDED_DEPENDENT_EXTRACTION_TARGETS_REP
#define INCLUDED_DEPENDENT_EXTRACTION_TARGETS_REP

#include <cstdint>
#include <dependent_extraction_targets_inner.h>

struct DependentExtractionTargets {
  template <typename T1> static List<T1> rep(const T1 &z, uint64_t n) {
    if (n <= 0) {
      return List<T1>::nil();
    } else {
      uint64_t m = n - 1;
      return List<T1>::cons(z, rep<T1>(z, m));
    }
  }
};

#endif // INCLUDED_DEPENDENT_EXTRACTION_TARGETS_REP
