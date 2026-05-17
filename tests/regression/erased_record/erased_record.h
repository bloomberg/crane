#ifndef INCLUDED_ERASED_RECORD
#define INCLUDED_ERASED_RECORD

struct ErasedRecord {
  struct ManyProps {
    uint64_t field0;
    uint64_t field1;
    uint64_t field2;
    uint64_t field3;
    uint64_t field4;

    // ACCESSORS
    ManyProps clone() const {
      return ManyProps{(*this).field0, (*this).field1, (*this).field2,
                       (*this).field3, (*this).field4};
    }
  };

  static uint64_t complex_match(const ManyProps &r);
  static uint64_t unusual_body(const ManyProps &r);

  struct MostlyProps {
    uint64_t real1;
    uint64_t real2;
    uint64_t real3;

    // ACCESSORS
    MostlyProps clone() const {
      return MostlyProps{(*this).real1, (*this).real2, (*this).real3};
    }
  };

  static uint64_t access_mostly_props(const MostlyProps &r);
  static inline const uint64_t test1 = complex_match(ManyProps{
      UINT64_C(1), UINT64_C(2), UINT64_C(3), UINT64_C(4), UINT64_C(5)});
  static inline const uint64_t test2 = unusual_body(ManyProps{
      UINT64_C(1), UINT64_C(2), UINT64_C(3), UINT64_C(4), UINT64_C(5)});
  static inline const uint64_t test3 =
      access_mostly_props(MostlyProps{UINT64_C(5), UINT64_C(10), UINT64_C(15)});
};

#endif // INCLUDED_ERASED_RECORD
