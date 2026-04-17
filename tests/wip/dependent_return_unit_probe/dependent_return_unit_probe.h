#ifndef INCLUDED_DEPENDENT_RETURN_UNIT_PROBE
#define INCLUDED_DEPENDENT_RETURN_UNIT_PROBE

#include <any>
#include <type_traits>
#include <utility>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

enum class Unit { e_TT };
enum class Bool0 { e_TRUE0, e_FALSE0 };

struct DependentReturnUnitProbe {
  static std::any dep(const Bool0 b);
  static inline const Unit sample_unit = []() {
    dep(Bool0::e_TRUE0);
    return Unit::e_TT;
  }();
  static inline const Bool0 sample_bool = dep(Bool0::e_FALSE0);
};

#endif // INCLUDED_DEPENDENT_RETURN_UNIT_PROBE
