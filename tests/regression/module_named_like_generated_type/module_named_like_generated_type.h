#ifndef INCLUDED_MODULE_NAMED_LIKE_GENERATED_TYPE
#define INCLUDED_MODULE_NAMED_LIKE_GENERATED_TYPE

#include <cstdint>

/// A module whose name is the one Crane picks for a generated type — Nat for
/// Rocq's nat, Bool0 for bool — is emitted as a struct nested inside
/// that type, giving "member 'ModuleNamedLikeGeneratedType' has the same name
/// as its class".  The clash is with a name Crane invented, so no amount of
/// care on the Rocq side avoids it.
struct Nat {
  static inline const uint64_t k = UINT64_C(1);
};

struct ModuleNamedLikeGeneratedType {
  static inline const uint64_t run = Nat::k;
};

#endif // INCLUDED_MODULE_NAMED_LIKE_GENERATED_TYPE
