#ifndef INCLUDED_LOCAL_MUTUAL_PARTNER_TYPE_ARG
#define INCLUDED_LOCAL_MUTUAL_PARTNER_TYPE_ARG

#include "fn.h"
#include <cstdint>

/// A local mutual group whose partner g, not the member f the group is
/// projected to, takes a type argument.  Dummy elimination
/// (kill_dummy_fix) dropped the erased binders of the projected member
/// alone, and only where it had some, so g kept a parameter for A
/// while f's call to it, its dummy argument dropped, passed none: g
/// took one argument more than it was given.  Every member's erased
/// binders go, each member's calls adjusted.
struct LocalMutualPartnerTypeArg {
  static uint64_t run(uint64_t _x, uint64_t n);
};

#endif // INCLUDED_LOCAL_MUTUAL_PARTNER_TYPE_ARG
