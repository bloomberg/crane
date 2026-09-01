#include "eta_match_returns_fun.h"

uint64_t EtaMatchReturnsFun::lookup(
    const List<std::pair<uint64_t, std::function<uint64_t(uint64_t)>>> &l,
    uint64_t k, uint64_t _x0) {
  return [=]() mutable -> std::function<uint64_t(uint64_t)> {
    if (std::holds_alternative<typename List<
            std::pair<uint64_t, std::function<uint64_t(uint64_t)>>>::Nil>(
            l.v())) {
      return [](uint64_t x) { return x; };
    } else {
      const auto &[a0, a1] = std::get<typename List<
          std::pair<uint64_t, std::function<uint64_t(uint64_t)>>>::Cons>(l.v());
      const List<std::pair<uint64_t, std::function<uint64_t(uint64_t)>>>
          &a1_value = *a1;
      if (a0.first == k) {
        return [=](uint64_t _x0) mutable -> uint64_t { return a0.second(_x0); };
      } else {
        return [=](uint64_t _x0) mutable -> uint64_t {
          return lookup(a1_value, k, _x0);
        };
      }
    }
  }()(_x0);
}
