#ifndef INCLUDED_LET_POLY_FN_INSTANCE
#define INCLUDED_LET_POLY_FN_INSTANCE

#include <cstdint>

/// A let-bound polymorphic function is lifted to a template, and the lifted
/// template's arity is taken from the lambda.  Instantiating it at a function
/// type and applying the result absorbs the extra argument into the same call,
/// so g 4 is emitted as a second argument to the one-parameter _anon_f.
struct LetPolyFnInstance {
  static constexpr uint64_t test = UINT64_C(8);
};

#endif // INCLUDED_LET_POLY_FN_INSTANCE
