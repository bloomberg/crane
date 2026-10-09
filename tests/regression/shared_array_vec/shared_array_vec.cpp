#include "shared_array_vec.h"

uint64_t SharedArrayVec::vec_sum(const crane::shared_array<uint64_t> &v) {
  if (v.empty()) {
    return UINT64_C(0);
  } else {
    const uint64_t &h = v.front();
    auto t = v.drop(1);
    return (h + vec_sum(t));
  }
}
