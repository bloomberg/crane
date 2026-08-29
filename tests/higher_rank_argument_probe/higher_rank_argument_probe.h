#ifndef INCLUDED_HIGHER_RANK_ARGUMENT_PROBE
#define INCLUDED_HIGHER_RANK_ARGUMENT_PROBE

#include <any>

enum class Bool0 { TRUE_, FALSE_ };

struct HigherRankArgumentProbe {
  template <typename F0> static Bool0 call_poly(F0 &&f) {
    return std::any_cast<Bool0>(f(Bool0::TRUE_));
  }

  static inline const Bool0 sample = call_poly([](const auto &x) { return x; });
};

#endif // INCLUDED_HIGHER_RANK_ARGUMENT_PROBE
