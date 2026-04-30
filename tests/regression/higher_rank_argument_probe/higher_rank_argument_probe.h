#ifndef INCLUDED_HIGHER_RANK_ARGUMENT_PROBE
#define INCLUDED_HIGHER_RANK_ARGUMENT_PROBE

#include <any>
#include <memory>
#include <optional>
#include <type_traits>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

enum class Bool0 { e_TRUE0, e_FALSE0 };

struct HigherRankArgumentProbe {
  template <typename F0> static Bool0 call_poly(F0 &&f) {
    return std::any_cast<Bool0>(f(Bool0::e_TRUE0));
  }

  static inline const Bool0 sample =
      call_poly([](const std::any x) { return x; });
};

#endif // INCLUDED_HIGHER_RANK_ARGUMENT_PROBE
