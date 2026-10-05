#ifndef INCLUDED_PATHOLOGICAL_RECORD
#define INCLUDED_PATHOLOGICAL_RECORD

#include "obj.h"
#include <cstdint>

struct PathologicalRecord {
  struct Rec {
    uint64_t f1;
    uint64_t f2;
    uint64_t f3;
  };

  static uint64_t hof_access(const Rec &r);
  static uint64_t nested_lets(const Rec &r);
  static uint64_t conditional_access(const Rec &r, bool flag);
  static uint64_t countdown(uint64_t n, const Rec &r);
  static uint64_t double_match(const Rec &r1, const Rec &r2);
  static uint64_t closure_over_fields(const Rec &r, uint64_t x);
  static constexpr uint64_t use_closure = UINT64_C(16);
  static uint64_t guarded_pattern(const Rec &r);

  struct BigRec {
    uint64_t bf1;
    uint64_t bf2;
    uint64_t bf3;
    uint64_t bf4;
    uint64_t bf5;
  };

  static uint64_t scrambled_access(const BigRec &r);
  static uint64_t repeated_access(const BigRec &r);
  static constexpr uint64_t test1 = UINT64_C(6);
  static constexpr uint64_t test2 = UINT64_C(15);
  static constexpr uint64_t test3 = UINT64_C(108);
};

#endif // INCLUDED_PATHOLOGICAL_RECORD
