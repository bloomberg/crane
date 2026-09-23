#include "eta_match_returns_fun.h"

uint64_t EtaMatchReturnsFun::lookup(
    const List<std::pair<uint64_t, std::function<uint64_t(uint64_t)>>> &l,
    uint64_t k, uint64_t x0_) {
  if (std::holds_alternative<typename List<
          std::pair<uint64_t, std::function<uint64_t(uint64_t)>>>::Nil>(
          l.v())) {
    return x0_;
  } else {
    const auto &[a0, a1] = std::get<typename List<
        std::pair<uint64_t, std::function<uint64_t(uint64_t)>>>::Cons>(l.v());
    if (a0.first == k) {
      return a0.second(x0_);
    } else {
      return lookup(*a1, k, x0_);
    }
  }
}
