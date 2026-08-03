#include "guard_compare_label_collision.h"

/// Regression test for the `Crane Guard Compare` Label-keying bug (see
/// docs/scan/117-guard-compare-directives-are-keyed-by-final-label-and-can-affect-unrelated-functions.md).
///
/// `guard_compare_table` in src/table.ml used to be keyed by `Label.t`
/// (`KerName.label`, i.e. just the trailing identifier, dropping the module
/// path), so two constants named compare in unrelated modules would
/// collide in the table: registering a guard for one would silently guard
/// the other too, even though it was never named in any Crane Guard
/// Compare directive. It is now keyed by full GlobRef.t (via Refmap',
/// matching the customs table's convention), so only the exact constant
/// named in a directive is affected.
///
/// OK.compare is an ordinary Fixpoint-recursive comparator returning the
/// plain extraction-primitive comparison type -- the shape Crane Guard
/// Compare's codegen supports. Ordered.compare mimics a
/// UsualOrderedType-module-style comparator (used throughout FSet/FMap-
/// backed structures, e.g. `SllSubparserAsUOT`/`CacheKeyAsUOT` in
/// parse-a-lot's `SLLPrediction.v`), returning the dependent
/// OrderedType.Compare lt eq x y sig -- a different C++ type. Only
/// OK.compare is guarded below; Ordered.compare must extract and compile
/// unaffected.
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
