#ifndef INCLUDED_POLYMORPHIC_FUNCTION_FIELD_PROBE
#define INCLUDED_POLYMORPHIC_FUNCTION_FIELD_PROBE

#include "crane_fn.h"
#include "fn.h"
#include "obj.h"
#include <any>

enum class Bool0;
enum class Bool0 { TRUE_, FALSE_ };

struct PolymorphicFunctionFieldProbe {
  struct poly {
    crane::fn<crane::obj(crane::obj)> apply;
  };

  template <typename T1> static T1 apply(const poly &p0, const T1 &x) {
    return crane_any_cast<T1>(p0.apply(x));
  }

  static inline const poly p =
      poly{crane_erase_fn<crane::obj>([](const auto &x) { return x; })};
  static inline const Bool0 sample_bool = apply<Bool0>(p, Bool0::TRUE_);
};

#endif // INCLUDED_POLYMORPHIC_FUNCTION_FIELD_PROBE
