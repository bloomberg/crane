#include "local_record_closures.h"

uint64_t LocalRecordClosures::use_local(uint64_t n) {
  return (((UINT64_C(3) * UINT64_C(2)) + n) + (n * UINT64_C(2)));
}

LocalRecordClosures::ops LocalRecordClosures::make(uint64_t n) {
  return ops{[=](uint64_t x) { return (x * n); },
             [=](uint64_t x) { return (x + n); }};
}

uint64_t LocalRecordClosures::two_records(uint64_t a, uint64_t b) {
  return ((UINT64_C(1) + a) + (UINT64_C(2) * b));
}
