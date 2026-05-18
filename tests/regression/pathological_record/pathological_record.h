#ifndef INCLUDED_PATHOLOGICAL_RECORD
#define INCLUDED_PATHOLOGICAL_RECORD

#include <any>

struct PathologicalRecord {
  struct Rec {
    uint64_t f1;
    uint64_t f2;
    uint64_t f3;

    // ACCESSORS
    Rec clone() const { return Rec{(*this).f1, (*this).f2, (*this).f3}; }
  };

  static uint64_t hof_access(const Rec &r);
  static uint64_t nested_lets(const Rec &r);
  static uint64_t conditional_access(const Rec &r, bool flag);
  static uint64_t countdown(uint64_t n, const Rec &r);
  static uint64_t double_match(const Rec &r1, const Rec &r2);
  static uint64_t closure_over_fields(const Rec &r, uint64_t x);
  static inline const uint64_t use_closure = closure_over_fields(
      Rec{UINT64_C(1), UINT64_C(2), UINT64_C(3)}, UINT64_C(10));
  static uint64_t guarded_pattern(const Rec &r);

  struct BigRec {
    uint64_t bf1;
    uint64_t bf2;
    uint64_t bf3;
    uint64_t bf4;
    uint64_t bf5;

    // ACCESSORS
    BigRec clone() const {
      return BigRec{(*this).bf1, (*this).bf2, (*this).bf3, (*this).bf4,
                    (*this).bf5};
    }
  };

  static uint64_t scrambled_access(const BigRec &r);
  static uint64_t repeated_access(const BigRec &r);
  static inline const uint64_t test1 =
      hof_access(Rec{UINT64_C(1), UINT64_C(2), UINT64_C(3)});
  static inline const uint64_t test2 =
      nested_lets(Rec{UINT64_C(4), UINT64_C(5), UINT64_C(6)});
  static inline const uint64_t test3 =
      double_match(Rec{UINT64_C(1), UINT64_C(2), UINT64_C(3)},
                   Rec{UINT64_C(4), UINT64_C(5), UINT64_C(6)});
};

#endif // INCLUDED_PATHOLOGICAL_RECORD
