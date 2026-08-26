#ifndef INCLUDED_SIG_FUN_PAYLOAD
#define INCLUDED_SIG_FUN_PAYLOAD

#include <any>
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

struct SigFunPayload {
  static inline const Sig<std::function<uint64_t(uint64_t)>> mk =
      Sig<std::function<uint64_t(uint64_t)>>::exist(
          [](uint64_t x) { return (x + UINT64_C(1)); });
  static inline const uint64_t go = []() {
    const auto &_sv0 = mk;
    const auto &[x0] = _sv0;
    return std::any_cast<std::function<std::any(std::any)>>(x0)(UINT64_C(4));
  }();
};

#endif // INCLUDED_SIG_FUN_PAYLOAD
