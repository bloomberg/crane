#ifndef INCLUDED_FIX_CHAIN_BUILD
#define INCLUDED_FIX_CHAIN_BUILD

#include <functional>
#include <utility>

struct FixChainBuild {
  static std::pair<uint64_t, std::function<uint64_t(uint64_t)>>
  build_chain(uint64_t n);
  static inline const uint64_t test1 = []() -> uint64_t {
    auto [base, f] = build_chain(UINT64_C(1));
    return (base + f(UINT64_C(2)));
  }();
  static inline const uint64_t test2 = []() -> uint64_t {
    auto [base, f] = build_chain(UINT64_C(2));
    return (base + f(UINT64_C(0)));
  }();
  static inline const uint64_t test3 = []() -> uint64_t {
    auto [base, f] = build_chain(UINT64_C(3));
    return (base + f(UINT64_C(0)));
  }();
};

#endif // INCLUDED_FIX_CHAIN_BUILD
