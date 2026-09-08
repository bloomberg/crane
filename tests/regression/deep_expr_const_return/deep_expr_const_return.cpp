#include "deep_expr_const_return.h"

/// An expression nested past the depth limit is rewritten into a sequence of
/// bindings inside an immediately-invoked lambda.  The lambda is given the
/// expression's own type as its trailing return type, and for a const-
/// qualified scalar that is -> const uint64_t, which -Wignored-qualifiers
/// rejects under -Werror.
uint64_t DeepExprConstReturn::f(uint64_t n) { return (n + UINT64_C(1)); }
