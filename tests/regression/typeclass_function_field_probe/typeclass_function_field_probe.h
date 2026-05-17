#ifndef INCLUDED_TYPECLASS_FUNCTION_FIELD_PROBE
#define INCLUDED_TYPECLASS_FUNCTION_FIELD_PROBE

#include <concepts>
#include <utility>

enum class Bool0 { TRUE_, FALSE_ };

struct Datatypes {
  static Bool0 negb(Bool0 b);
};

template <typename I, typename A>
concept HasEndo = requires(A a0) {
  { I::endo(a0) } -> std::convertible_to<A>;
};

struct TypeclassFunctionFieldProbe {
  struct boolEndo {
    constexpr static Bool0 endo(Bool0 a0) { return Datatypes::negb(a0); }
  };

  static_assert(HasEndo<boolEndo, Bool0>);

  template <typename _tcI0, typename T1> static T1 use(const T1 &x) {
    return _tcI0::endo(_tcI0::endo(x));
  }

  static inline const Bool0 sample = use<boolEndo, Bool0>(Bool0::TRUE_);
};

#endif // INCLUDED_TYPECLASS_FUNCTION_FIELD_PROBE
