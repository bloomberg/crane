#ifndef INCLUDED_EMPTY_INDUCTIVE_ELIM
#define INCLUDED_EMPTY_INDUCTIVE_ELIM

#include <any>
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

  template <typename T1> static T1 void_rec() {
    throw std::logic_error("absurd case");
  }

  static uint64_t absurd();
  static uint64_t g(const std::optional<std::any> &o);
  static inline const uint64_t test = g(std::optional<std::any>());
};

#endif // INCLUDED_EMPTY_INDUCTIVE_ELIM
