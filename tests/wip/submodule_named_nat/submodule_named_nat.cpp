#include "submodule_named_nat.h"

/// A submodule named Nat collides with the runtime Nat struct.  Inside the
/// generated struct Nat, the unqualified return type Nat resolves to the
/// submodule rather than to the global inductive:
///
/// error: return type of out-of-line definition of
/// 'SubmoduleNamedNat::Nat::succ' differs from that in the declaration
/// error: no member named 's' in 'SubmoduleNamedNat::Nat'
///
/// Unlike shadow_runtime_nat, the shadowing name here is a *module*, so the
/// fix has to qualify references from inside module scopes too.
Nat SubmoduleNamedNat::Nat::succ(Nat n) { return Nat::s(std::move(n)); }

Nat SubmoduleNamedNat::run(const Nat &_x0) { return Nat::succ(_x0); }
