#include "unit_returning_callback_map.h"

/// A unit-returning function becomes void in a higher-order position,
/// which does not match the std::monostate element type the surrounding
/// map was instantiated with.
void UnitReturningCallbackMap::noop(uint64_t) { return; }
