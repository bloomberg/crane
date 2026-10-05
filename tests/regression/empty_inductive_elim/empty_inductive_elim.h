#ifndef INCLUDED_EMPTY_INDUCTIVE_ELIM
#define INCLUDED_EMPTY_INDUCTIVE_ELIM

#include "obj.h"
#include <cstdint>
#include <memory>
#include <optional>
#include <stdexcept>

/// Eliminating an inductive with no constructors is unreachable, and Crane
/// emits []() { throw std::logic_error("absurd case"); }() for it.  That
/// lambda's deduced return type is void, so it cannot initialise the value
/// the elimination is supposed to produce.
struct EmptyInductiveElim {
  template <typename T1> static T1 void_rect() {
    throw std::logic_error("absurd case");
  }

  template <typename T1> static const T1 &void_rec() {
    static const T1 v = [](crane::obj) {
      throw std::logic_error("untranslatable curried proof term");
    };
    return v;
  }

  static uint64_t absurd();
  static uint64_t g(const std::optional<crane::obj> &o);
  static constexpr uint64_t test = UINT64_C(0);
};

#endif // INCLUDED_EMPTY_INDUCTIVE_ELIM
