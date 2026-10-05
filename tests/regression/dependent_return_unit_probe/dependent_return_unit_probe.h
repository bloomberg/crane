#ifndef INCLUDED_DEPENDENT_RETURN_UNIT_PROBE
#define INCLUDED_DEPENDENT_RETURN_UNIT_PROBE

#include "obj.h"
#include <utility>

enum class Unit;
enum class Bool0;
enum class Unit { TT };
enum class Bool0 { TRUE_, FALSE_ };

struct DependentReturnUnitProbe {
  static crane::obj dep(Bool0 b);
  static inline const Unit sample_unit = []() {
    crane::any_cast<Unit>(dep(Bool0::TRUE_));
    return Unit::TT;
  }();
  static inline const Bool0 sample_bool =
      crane::any_cast<Bool0>(dep(Bool0::FALSE_));
};

#endif // INCLUDED_DEPENDENT_RETURN_UNIT_PROBE
