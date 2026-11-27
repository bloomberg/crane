#pragma once

#include "crane_fn.h"
#include "obj.h"
#include <concepts>
#include <crane_itree.h>
#include <cstdint>
#include <memory>
#include <stdexcept>
#include <string>
#include <string_view>
#include <utility>
#include <variant>

template <typename T1> struct code_const;
template <typename Err> struct ExceptE;
struct Err;
enum class STRefs;
template <typename I, typename V, typename A>
concept Code = requires {
  { I::code() } -> std::convertible_to<uint64_t>;
};

struct Nat {};

struct FibstCofixReproTests {
  /// Reproduces a version of fibST in STMonadtest.v.  It recurses without
  /// end by construction: n is not decremented on each recursive call.
  /// The test checks that the divergence is a constant-stack loop.
  ///
  /// Extraction used to fail with "a type mapped to nothing reached the
  /// printer: STEvent".  Three defects: the section's Lets are lets at
  /// the head of the body, and db_from_rel_context numbered them as type
  /// variables, so the annotation of go named no variable of the
  /// declaration and seeded nothing; a let cofix was not seeded from its
  /// annotation at all (only a let fix was); and seeding opened every
  /// Unknown of an annotation to a meta, including the argument the
  /// unapplied family STEvent ... +' exceptE Err is eta-expanded at,
  /// which nothing solves.  The open metas generalised into type variables
  /// of go's own, so go was lifted to a template whose call spelled the
  /// skipped STEvent.  Then, generated in place, Core_plan.Closures
  /// took go to escape, as a cofixpoint's body is suspended -- but a
  /// cofixpoint into a monad generated as sequencing is not.
  static uint64_t fibst_repro(uint64_t x0_);
};

template <typename Err> struct ExceptE {
  // DATA
  Err a0;

  // ACCESSORS
  ExceptE<Err> clone() const { return {a0}; }

  template <typename CraneU> operator ExceptE<CraneU>() const {
    return {[&]() -> CraneU {
      if constexpr (crane_convertible<CraneU, const Err &>) {
        return crane_convert<CraneU>(a0);
      } else {
        throw std::logic_error("unreachable: inactive constructor field at "
                               "this instantiation");
      }
    }()};
  }

  // CREATORS
  static ExceptE<Err> Throw_(Err a0) { return {std::move(a0)}; }
};

struct Err {
  // DATA
  std::string x;

  // ACCESSORS
  Err clone() const { return {x}; }

  // CREATORS
  static Err error(std::string x) { return {std::move(x)}; }
};

enum class STRefs { BUILD_STREFS };

template <typename T1> struct code_const {
  constexpr static uint64_t code() { return UINT64_C(0); }
};

/// Reproduces a version of fibST in STMonadtest.v.  It recurses without
/// end by construction: n is not decremented on each recursive call.
/// The test checks that the divergence is a constant-stack loop.
///
/// Extraction used to fail with "a type mapped to nothing reached the
/// printer: STEvent".  Three defects: the section's Lets are lets at
/// the head of the body, and db_from_rel_context numbered them as type
/// variables, so the annotation of go named no variable of the
/// declaration and seeded nothing; a let cofix was not seeded from its
/// annotation at all (only a let fix was); and seeding opened every
/// Unknown of an annotation to a meta, including the argument the
/// unapplied family STEvent ... +' exceptE Err is eta-expanded at,
/// which nothing solves.  The open metas generalised into type variables
/// of go's own, so go was lifted to a template whose call spelled the
/// skipped STEvent.  Then, generated in place, Core_plan.Closures
/// took go to escape, as a cofixpoint's body is suspended -- but a
/// cofixpoint into a monad generated as sequencing is not.
uint64_t fibst_repro(STRefs _x, uint64_t n);
