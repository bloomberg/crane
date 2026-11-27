#include "sigma_types.h"

SigT<uint64_t, crane::obj> SigmaTypes::nat_with_double(uint64_t n) {
  return SigT<uint64_t, crane::obj>::existt(n + n, crane::obj());
}

uint64_t SigmaTypes::positive_succ(uint64_t n) { return (n + 1); }

uint64_t SigmaTypes::get_positive(uint64_t n) { return positive_succ(n); }

uint64_t SigmaTypes::double_positive(uint64_t n) {
  uint64_t p = positive_succ(n);
  return p + p;
}

uint64_t SigmaTypes::use_nat_double(uint64_t n) {
  return nat_with_double(n).projT1();
}

List<uint64_t> SigmaTypes::positives_up_to(uint64_t k) {
  if (k <= 0) {
    return List<uint64_t>::nil();
  } else {
    uint64_t k_ = k - 1;
    return List<uint64_t>::cons(positive_succ(k_), positives_up_to(k_));
  }
}
