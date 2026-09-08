#ifndef INCLUDED_LET_POLY_FN_INSTANCE
#define INCLUDED_LET_POLY_FN_INSTANCE

#include <functional>

/// A let-bound polymorphic function is lifted to a template, and the lifted
/// template's arity is taken from the lambda.  Instantiating it at a function
/// type and applying the result absorbs the extra argument into the same call,
/// so g 4 is emitted as a second argument to the one-parameter _anon_f.
struct LetPolyFnInstance {
  template <typename T1> static T1 _anon_f(const T1 x) { return x; }

  static inline const uint64_t test = []() {
    return (_anon_f(UINT64_C(3)) + _anon_f(std::function([](uint64_t y) {
              return (y + UINT64_C(1));
            }))(UINT64_C(4)));
  }();
};

#endif // INCLUDED_LET_POLY_FN_INSTANCE
