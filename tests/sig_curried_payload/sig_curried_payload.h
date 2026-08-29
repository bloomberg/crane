#ifndef INCLUDED_SIG_CURRIED_PAYLOAD
#define INCLUDED_SIG_CURRIED_PAYLOAD

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

struct SigCurriedPayload {
  static inline const Sig<std::function<uint64_t(uint64_t, uint64_t)>> mk =
      Sig<std::function<uint64_t(uint64_t, uint64_t)>>::exist(
          [](uint64_t _x0, uint64_t _x1) -> uint64_t { return (_x0 + _x1); });
  static inline const uint64_t go = []() {
    const auto &_sv0 = mk;
    const auto &[x0] = _sv0;
    return x0(UINT64_C(1), UINT64_C(2));
  }();
};

#endif // INCLUDED_SIG_CURRIED_PAYLOAD
