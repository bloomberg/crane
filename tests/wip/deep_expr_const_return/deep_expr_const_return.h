#ifndef INCLUDED_DEEP_EXPR_CONST_RETURN
#define INCLUDED_DEEP_EXPR_CONST_RETURN

#include <utility>

/// An expression nested past the depth limit is rewritten into a sequence of
/// bindings inside an immediately-invoked lambda.  The lambda is given the
/// expression's own type as its trailing return type, and for a const-
/// qualified scalar that is -> const uint64_t, which -Wignored-qualifiers
/// rejects under -Werror.
struct DeepExprConstReturn {
  static uint64_t f(uint64_t n);
  static inline const uint64_t test = []() -> const uint64_t {
    auto _lit0 = f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(
        f(f(f(f(f(f(f(f(f(f(f(f(f(f(UINT64_C(0))))))))))))))))))))))))))))))));
    auto _lit1 = f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(
        f(f(f(f(f(f(f(f(f(f(f(f(std::move(_lit0)))))))))))))))))))))))))))))));
    auto _lit2 = f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(
        f(f(f(f(f(f(f(f(f(f(f(f(std::move(_lit1)))))))))))))))))))))))))))))));
    auto _lit3 = f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(
        f(f(f(f(f(f(f(f(f(f(f(f(std::move(_lit2)))))))))))))))))))))))))))))));
    return f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(
        f(f(f(f(f(f(f(f(f(f(f(f(f(std::move(_lit3))))))))))))))))))))))))))))));
  }();
};

#endif // INCLUDED_DEEP_EXPR_CONST_RETURN
