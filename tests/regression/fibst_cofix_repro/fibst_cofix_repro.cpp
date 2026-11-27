#include "fibst_cofix_repro.h"

/// Reproduces a version of fibST in STtest.v.  It recurses without
/// end by construction: n is not decremented on each recursive call.
/// The test checks that the divergence is a constant-stack loop.
///
/// Extraction used to fail with "a type mapped to nothing reached the
/// printer: ST.Event".  Three defects: the section's Lets are lets at
/// the head of the body, and db_from_rel_context numbered them as type
/// variables, so the annotation of go named no variable of the
/// declaration and seeded nothing; a let cofix was not seeded from its
/// annotation at all (only a let fix was); and seeding opened every
/// Unknown of an annotation to a meta, including the argument the
/// unapplied family ST.Event ... +' exceptE Err is eta-expanded at,
/// which nothing solves.  The open metas generalised into type variables
/// of go's own, so go was lifted to a template whose call spelled the
/// skipped ST.Event.  Then, generated in place, Core_plan.Closures
/// took go to escape, as a cofixpoint's body is suspended -- but a
/// cofixpoint into a monad generated as sequencing is not.
uint64_t fibst_repro(uint64_t n) {
  auto go = [&](uint64_t *x_view, uint64_t *y_view) -> uint64_t {
    // Loop replaces the tail recursion: each recursive call updates the loop
    // variables.
    while (true) {
      if (n <= 0) {
        return *x_view;
      } else {
        uint64_t _x0 = n - 1;
        uint64_t x_ = *x_view;
        uint64_t y_ = *y_view;
        *x_view = y_;
        *y_view = (x_ + y_);
      }
    }
  };
  if (n <= UINT64_C(2)) {
    return n;
  } else {
    uint64_t x = UINT64_C(0);
    uint64_t y = UINT64_C(1);
    return go(&x, &y);
  }
}

/// Reproduces a version of fibST in STtest.v.  It recurses without
/// end by construction: n is not decremented on each recursive call.
/// The test checks that the divergence is a constant-stack loop.
///
/// Extraction used to fail with "a type mapped to nothing reached the
/// printer: ST.Event".  Three defects: the section's Lets are lets at
/// the head of the body, and db_from_rel_context numbered them as type
/// variables, so the annotation of go named no variable of the
/// declaration and seeded nothing; a let cofix was not seeded from its
/// annotation at all (only a let fix was); and seeding opened every
/// Unknown of an annotation to a meta, including the argument the
/// unapplied family ST.Event ... +' exceptE Err is eta-expanded at,
/// which nothing solves.  The open metas generalised into type variables
/// of go's own, so go was lifted to a template whose call spelled the
/// skipped ST.Event.  Then, generated in place, Core_plan.Closures
/// took go to escape, as a cofixpoint's body is suspended -- but a
/// cofixpoint into a monad generated as sequencing is not.
uint64_t FibstCofixReproTests::fibst_repro(uint64_t x0_) {
  return ::fibst_repro(x0_);
}
