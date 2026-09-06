#include "module_local_return_type.h"

/// An out-of-line definition spells its return type *before* the qualified
/// function name, so the enclosing struct's scope is not yet open there.  A
/// function returning a type declared in a nested module is emitted as
/// M::t ModuleLocalReturnType::make(...), and M is undeclared at that
/// point.  Parameter types, which come after the qualified name, are fine.
M::t ModuleLocalReturnType::make(uint64_t n) { return M::t::c(n); }
