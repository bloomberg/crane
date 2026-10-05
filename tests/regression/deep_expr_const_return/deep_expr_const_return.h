#ifndef INCLUDED_DEEP_EXPR_CONST_RETURN
#define INCLUDED_DEEP_EXPR_CONST_RETURN

#include <cstdint>

/// An expression nested past the depth limit is rewritten into a sequence of
/// bindings inside an immediately-invoked lambda.  The lambda is given the
/// expression's own type as its trailing return type, and for a const-
/// qualified scalar that is -> const uint64_t, which -Wignored-qualifiers
/// rejects under -Werror.
struct DeepExprConstReturn {
  static uint64_t f(uint64_t n);
  static constexpr uint64_t test = UINT64_C(150);
};

#endif // INCLUDED_DEEP_EXPR_CONST_RETURN
