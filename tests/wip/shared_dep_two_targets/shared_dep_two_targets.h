#ifndef INCLUDED_SHARED_DEP_TWO_TARGETS
#define INCLUDED_SHARED_DEP_TWO_TARGETS

#include <utility>

/// Two extraction targets that both depend on a definition outside either of
/// them each emit their own copy of it.  The two headers are individually
/// well-formed, but a translation unit that includes both sees Col defined
/// twice.  Nothing in the generated code marks the copies as the same entity.
enum class Col { RED, GREEN };
Col flip(Col c);

struct SharedDepTwoTargets {
  static inline const bool test = []() {
    switch (flip(Col::RED)) {
    case Col::RED: {
      return false;
    }
    case Col::GREEN: {
      return true;
    }
    default:
      std::unreachable();
    }
  }();
};

#endif // INCLUDED_SHARED_DEP_TWO_TARGETS
