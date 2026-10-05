#ifndef INCLUDED_VALUE_TYPE_MATCH_FIX
#define INCLUDED_VALUE_TYPE_MATCH_FIX

#include "fn.h"
#include <cstdint>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

struct ValueTypeMatchFix {
  /// A non-recursive inductive (will be a value type).
  struct triple {
    // DATA
    uint64_t a0;
    uint64_t a1;
    uint64_t a2;

    // ACCESSORS
    triple clone() const { return {a0, a1, a2}; }

    // CREATORS
    static triple mktriple(uint64_t a0, uint64_t a1, uint64_t a2) {
      return {a0, a1, a2};
    }
  };

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, const uint64_t &, const uint64_t &,
                                   const uint64_t &>
  static T1 triple_rect(F0 &&f, const triple &t) {
    const auto &[a0, a1, a2] = t;
    return f(a0, a1, a2);
  }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, const uint64_t &, const uint64_t &,
                                   const uint64_t &>
  static T1 triple_rec(F0 &&f, const triple &t) {
    const auto &[a0, a1, a2] = t;
    return f(a0, a1, a2);
  }

  /// A fixpoint that captures a field from a value-type match.
  ///
  /// BUG HYPOTHESIS: triple is a value type (stack-allocated, non-recursive).
  /// When pattern matching on a value type, the fields are bound as
  /// references into the stack-allocated object. If a fixpoint captures
  /// these references by & and then escapes, the references dangle
  /// when the function returns and the value type is destroyed.
  ///
  /// This is different from pointer-based (shared_ptr) types where the
  /// field data lives on the heap and persists as long as the shared_ptr.
  static std::optional<crane::fn<uint64_t(uint64_t)>>
  make_adder_from_triple(const triple &t);
  /// test1: MkTriple 10 20 30 -> base=60, go(5) = 60+5 = 65.
  static constexpr uint64_t test1 = UINT64_C(65);
  /// test2: With noise between creation and use.
  static constexpr uint64_t test2 = UINT64_C(655);
  /// Direct capture of pattern fields (no intermediate let binding).
  static std::optional<crane::fn<uint64_t(uint64_t)>>
  make_field_adder(const triple &t);
  /// test3: MkTriple 42 0 0 -> a=42, go(3) = 42+3 = 45.
  static constexpr uint64_t test3 = UINT64_C(45);
};

#endif // INCLUDED_VALUE_TYPE_MATCH_FIX
