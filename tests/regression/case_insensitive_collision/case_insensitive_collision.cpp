#include "case_insensitive_collision.h"

/// Crane capitalises an inductive's name to form its C++ type, so the
/// inductive bar and the definition Bar both want to be Bar.  The
/// generated code then has to say enum Bar to name the type at all, and the
/// two are indistinguishable at the use site.
uint64_t CaseInsensitiveCollision::Bar0(CaseInsensitiveCollision::Bar b) {
  switch (b) {
  case Bar::B1: {
    return UINT64_C(3);
  }
  case Bar::B2: {
    return UINT64_C(4);
  }
  default:
    std::unreachable();
  }
}
