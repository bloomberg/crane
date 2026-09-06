#include "submodule_named_nat.h"

/// A submodule named Nat becomes a nested struct that shadows the runtime
/// Nat for every unqualified lookup inside its parent, so the runtime type
/// must be spelled ::Nat:
///
/// ::Nat SubmoduleNamedNat::Nat::succ(::Nat n)
///
/// Unlike shadow_runtime_nat, the shadowing name here is a *module*, which
/// carries no GlobRef.t of its own.
::Nat SubmoduleNamedNat::Nat::succ(::Nat n) { return ::Nat::s(std::move(n)); }

::Nat SubmoduleNamedNat::run(const ::Nat &x0_) { return Nat::succ(x0_); }
