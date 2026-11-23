#pragma once

#include "small_vector.h"
#include <atomic>
#include <conslist.h>
#include <cstdint>
#include <memory>
#include <optional>
#include <utility>
#include <variant>

struct Nat {
  static bool even(uint64_t n);
}; /// A memoised longest-prefix scan shaped like ParseALot's max_pref_fn_M,

/// over a list mapped to a cons list whose match template binds the tail as
/// a variable of its own (auto %b1a1 = %scrut.tail()) and the head by
/// reference.  The tail is a copy, not a part of the scrutinee: the call
/// entering the machine takes it by move.  The frame saved across the call
/// copies the head, a part of the list, before moving the list in after it,
/// instead of copying the list.
struct FrameSaveCopiedBinder {
  static bool accepting(const crane::list<uint64_t> &st);
  static crane::list<uint64_t> step(uint64_t a,
                                    const crane::list<uint64_t> &st);
  static std::optional<std::optional<std::pair<
      std::pair<crane::list<uint64_t>, crane::list<uint64_t>>, uint64_t>>>
  lookup(std::optional<uint64_t> m, uint64_t a);
  static std::pair<
      uint64_t,
      std::optional<std::pair<
          std::pair<crane::list<uint64_t>, crane::list<uint64_t>>, uint64_t>>>
  scan(std::optional<uint64_t> m, const crane::list<uint64_t> &s, uint64_t i,
       const crane::list<uint64_t> &st);
};
