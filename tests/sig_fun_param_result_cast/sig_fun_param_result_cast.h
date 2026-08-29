#ifndef INCLUDED_SIG_FUN_PARAM_RESULT_CAST
#define INCLUDED_SIG_FUN_PARAM_RESULT_CAST

#include <cassert>
#include <functional>
#include <utility>
#include <variant>

template <typename A> struct Sig {
  // DATA
  A x;

  // ACCESSORS
  Sig<A> clone() const { return {x}; }

  // CREATORS
  static Sig<A> exist(A x) { return {std::move(x)}; }
};

struct SigFunParamResultCast {
  static uint64_t apply_sig(const Sig<std::function<uint64_t(uint64_t)>> &f,
                            uint64_t n);
  static inline const Sig<std::function<uint64_t(uint64_t)>> idf =
      Sig<std::function<uint64_t(uint64_t)>>::exist(
          [](uint64_t n) { return n; });
  static inline const uint64_t go = apply_sig(idf, UINT64_C(2));
};

#endif // INCLUDED_SIG_FUN_PARAM_RESULT_CAST
