#include "sigma_types.h"

SigT<uint64_t, std::any> SigmaTypes::nat_with_double(uint64_t n) {
  return SigT<uint64_t, std::any>::existt((n + n), std::any());
}

Sig<uint64_t> SigmaTypes::positive_succ(uint64_t n) {
  return Sig<uint64_t>::exist((n + 1));
}

uint64_t SigmaTypes::get_positive(uint64_t n) {
  const auto &_sv = positive_succ(n);
  const auto &[x] = _sv;
  return x;
}

Sig<uint64_t> SigmaTypes::double_positive(uint64_t n) {
  Sig<uint64_t> p = positive_succ(n);
  return Sig<uint64_t>::exist(([=]() mutable {
    auto &[x] = p;
    return x;
  }() +
                               [=]() mutable {
                                 auto &[x0] = p;
                                 return x0;
                               }()));
}

uint64_t SigmaTypes::use_nat_double(uint64_t n) {
  return nat_with_double(n).projT1();
}

List<uint64_t> SigmaTypes::positives_up_to(uint64_t k) {
  if (k <= 0) {
    return List<uint64_t>::nil();
  } else {
    uint64_t k_ = k - 1;
    return List<uint64_t>::cons(
        [&]() {
          const auto &_sv = positive_succ(k_);
          const auto &[x] = _sv;
          return x;
        }(),
        positives_up_to(k_));
  }
}
