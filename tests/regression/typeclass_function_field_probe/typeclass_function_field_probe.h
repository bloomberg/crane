#ifndef INCLUDED_TYPECLASS_FUNCTION_FIELD_PROBE
#define INCLUDED_TYPECLASS_FUNCTION_FIELD_PROBE

#include <concepts>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

enum class Bool0 { e_TRUE0, e_FALSE0 };

struct Datatypes {
  __attribute__((pure)) static Bool0 negb(const Bool0 b);
};

template <typename I, typename t_A>
concept HasEndo = requires(t_A a0) {
  { I::endo(a0) } -> std::convertible_to<t_A>;
};

struct TypeclassFunctionFieldProbe {
  struct boolEndo {
    constexpr static Bool0 endo(Bool0 a0) { return Datatypes::negb(a0); }
  };

  static_assert(HasEndo<boolEndo, Bool0>);

  template <typename _tcI0, typename T1> static T1 use(const T1 x) {
    return _tcI0::endo(_tcI0::endo(x));
  }

  static inline const Bool0 sample = use<boolEndo, Bool0>(Bool0::e_TRUE0);
};

#endif // INCLUDED_TYPECLASS_FUNCTION_FIELD_PROBE
