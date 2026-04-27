#ifndef INCLUDED_DEPENDENT_RETURN_UNIT_PROBE
#define INCLUDED_DEPENDENT_RETURN_UNIT_PROBE

#include <any>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

enum class Unit { e_TT };
enum class Bool0 { e_TRUE0, e_FALSE0 };

struct DependentReturnUnitProbe {
  static std::any dep(const Bool0 b);
  static inline const Unit sample_unit = []() {
    std::any_cast<Unit>(dep(Bool0::e_TRUE0));
    return Unit::e_TT;
  }();
  static inline const Bool0 sample_bool =
      std::any_cast<Bool0>(dep(Bool0::e_FALSE0));
};

#endif // INCLUDED_DEPENDENT_RETURN_UNIT_PROBE
