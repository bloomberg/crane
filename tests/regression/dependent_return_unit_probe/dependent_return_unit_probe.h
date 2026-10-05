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
  static constexpr Unit sample_unit = Unit::TT;
  static constexpr Bool0 sample_bool = Bool0::FALSE_;
};

#endif // INCLUDED_DEPENDENT_RETURN_UNIT_PROBE
