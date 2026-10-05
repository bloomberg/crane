#ifndef INCLUDED_ERASED_RECORD
#define INCLUDED_ERASED_RECORD

#include <cstdint>

struct ErasedRecord {
  struct ManyProps {
    uint64_t field0;
    uint64_t field1;
    uint64_t field2;
    uint64_t field3;
    uint64_t field4;
  };

  static uint64_t complex_match(const ManyProps &r);
  static uint64_t unusual_body(const ManyProps &r);

  struct MostlyProps {
    uint64_t real1;
    uint64_t real2;
    uint64_t real3;
  };

  static uint64_t access_mostly_props(const MostlyProps &r);
  static constexpr uint64_t test1 = UINT64_C(15);
  static constexpr uint64_t test2 = UINT64_C(15);
  static constexpr uint64_t test3 = UINT64_C(30);
};

#endif // INCLUDED_ERASED_RECORD
