#include "name_matches_module.h"

/// A module becomes a C++ struct, so a definition or an inductive named after
/// its enclosing module becomes a member with the same name as its class,
/// which C++ forbids.  Both spellings are here: Inner inside module Inner,
/// and NameMatchesModule inside module NameMatchesModule.
uint64_t
NameMatchesModule::Inner::get(const NameMatchesModule::Inner::Inner0 &x) {
  const auto &[a0] = x;
  return a0;
}
