#include "guard_compare_label_collision.h"

/// Reproduces the documented `Crane Guard Compare` Label-keying bug (see
/// docs/scan/117-guard-compare-directives-are-keyed-by-final-label-and-can-affect-unrelated-functions.md).
///
/// `guard_compare_table` in src/table.ml is keyed by `Label.t`
/// (`KerName.label`, i.e. just the trailing identifier, dropping the module
/// path), not by full `GlobRef.t`. Two constants named compare in
/// unrelated modules therefore collide in the table: registering a guard
/// for one silently guards the other too, even though it is never named in
/// any Crane Guard Compare directive.
///
/// This matters because the guard's generated fast path is hardcoded to
/// return Datatypes::Comparison::EQ;, which only type-checks when the
/// target's return type really is the plain extraction-primitive
/// comparison type -- the shape ordinary Fixpoint-recursive comparators
/// have (e.g. OK.compare below, or `re_compare` in a real grammar's
/// lexer). UsualOrderedType-module-style comparators (used throughout
/// FSet/FMap-backed structures, e.g. `SllSubparserAsUOT`/`CacheKeyAsUOT` in
/// parse-a-lot's `SLLPrediction.v`) instead return the dependent
/// OrderedType.Compare lt eq x y sig -- a different C++ type. Ordered.t
/// below mimics that shape.
///
/// Expected (buggy) result: extracting this file and compiling the
/// generated C++ FAILS -- not because of anything wrong with Ordered.compare
/// itself, but because the Label collision injects an ill-typed
/// Datatypes::Comparison::EQ fast path into it, purely as a side effect of
/// guarding the unrelated OK.compare. A fix that keys `guard_compare_table`
/// by full GlobRef.t instead of Label.t should make this file extract
/// and compile cleanly (with the guard applied only to OK.compare).
/// An ordinary structural comparator returning the plain extraction
/// primitive comparison -- the only shape `Crane Guard Compare`'s
/// codegen actually supports. Guarding this one is fine: physical
/// identity of the two arguments trivially implies structural equality
/// for pure/immutable values.
Comparison OK::compare(const Nat &x, const Nat &y) {
  if (&y == &x) {
    return Comparison::EQ;
  }
  if (std::holds_alternative<typename Nat::O>(x.v())) {
    if (std::holds_alternative<typename Nat::O>(y.v())) {
      return Comparison::EQ;
    } else {
      return Comparison::LT;
    }
  } else {
    const auto &[a0] = std::get<typename Nat::S>(x.v());
    if (std::holds_alternative<typename Nat::O>(y.v())) {
      return Comparison::GT;
    } else {
      const auto &[a00] = std::get<typename Nat::S>(y.v());
      return compare(*a0, *a00);
    }
  }
}

/// An ordinary structural comparator returning the plain extraction
/// primitive comparison -- the only shape `Crane Guard Compare`'s
/// codegen actually supports. Guarding this one is fine: physical
/// identity of the two arguments trivially implies structural equality
/// for pure/immutable values.
Compare<Ordered::T> Ordered::compare(Ordered::T x, Ordered::T y) {
  if (&y == &x) {
    return Comparison::EQ;
  }
  switch (x) {
  case T::A: {
    switch (y) {
    case T::A: {
      return Compare<Ordered::T>::eq();
    }
    case T::B: {
      return Compare<Ordered::T>::lt();
    }
    default:
      std::unreachable();
    }
    break;
  }
  case T::B: {
    switch (y) {
    case T::A: {
      return Compare<Ordered::T>::gt();
    }
    case T::B: {
      return Compare<Ordered::T>::eq();
    }
    default:
      std::unreachable();
    }
    break;
  }
  default:
    std::unreachable();
  }
}
