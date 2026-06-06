#ifndef INCLUDED_FIX_CHAIN_BUILD
#define INCLUDED_FIX_CHAIN_BUILD

#include <functional>
#include <utility>

struct FixChainBuild {
  /// Recursive construction of a closure chain. Each level creates a
  /// local fixpoint that captures the current n AND the previous
  /// level's closure prev, then stores the fixpoint in a pair with
  /// its base value (preventing uncurrying).
  ///
  /// BUG: Each step fixpoint uses & capture, binding n (the
  /// current stack frame's parameter), prev (a local variable),
  /// and step itself. When build_chain returns, the stack frame
  /// is destroyed, and the returned closure holds dangling references.
  static std::pair<uint64_t, std::function<uint64_t(uint64_t)>>
  build_chain(uint64_t n);
  /// test1: build_chain(1) = (1, step1).
  /// step1(0) = 1.
  /// step1(2) = S(prev(step1(1))) = S(prev(S(prev(step1(0)))))
  /// = S(prev(S(prev(1)))) = S(prev(S(1))) = S(prev(2)) = S(2) = 3.
  /// Pair first + step1(2) = 1 + 3 = 4.
  static inline const uint64_t test1 = []() -> uint64_t {
    auto _cs = build_chain(UINT64_C(1));
    uint64_t base = std::move(_cs.first);
    std::function<uint64_t(uint64_t)> f = std::move(_cs.second);
    return (base + f(UINT64_C(2)));
  }();
  /// test2: build_chain(2).
  /// step1 captures prev=id, n=1. step2 captures prev=step1, n=2.
  /// step2(0) = 2. Result: 2 + step2(0) = 2 + 2 = 4.
  static inline const uint64_t test2 = []() -> uint64_t {
    auto _cs = build_chain(UINT64_C(2));
    uint64_t base = std::move(_cs.first);
    std::function<uint64_t(uint64_t)> f = std::move(_cs.second);
    return (base + f(UINT64_C(0)));
  }();
  /// test3: build_chain(3). More nesting = more dangling frames.
  /// step3(0) = 3. Result: 3 + 3 = 6.
  static inline const uint64_t test3 = []() -> uint64_t {
    auto _cs = build_chain(UINT64_C(3));
    uint64_t base = std::move(_cs.first);
    std::function<uint64_t(uint64_t)> f = std::move(_cs.second);
    return (base + f(UINT64_C(0)));
  }();
};

#endif // INCLUDED_FIX_CHAIN_BUILD
