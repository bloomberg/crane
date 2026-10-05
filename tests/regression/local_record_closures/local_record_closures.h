#ifndef INCLUDED_LOCAL_RECORD_CLOSURES
#define INCLUDED_LOCAL_RECORD_CLOSURES

#include "fn.h"
#include <cstdint>

struct LocalRecordClosures {
  /// A record of functions built and used in one place: each call through a
  /// field is that function's body at the call, and the record itself is gone.
  /// One that escapes keeps its representation.
  struct ops {
    crane::fn<uint64_t(uint64_t)> scale;
    crane::fn<uint64_t(uint64_t)> shift;
  };

  static uint64_t use_local(uint64_t n);
  static ops make(uint64_t n);
  static uint64_t two_records(uint64_t a, uint64_t b);
};

#endif // INCLUDED_LOCAL_RECORD_CLOSURES
