#ifndef INCLUDED_VALUE_TYPE_MATCH_FIX
#define INCLUDED_VALUE_TYPE_MATCH_FIX

#include <functional>
#include <memory>
#include <optional>
#include <type_traits>
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
    requires std::is_invocable_r_v<T1, F0 &, uint64_t &, uint64_t &, uint64_t &>
  static T1 triple_rect(F0 &&f, const triple &t) {
    const auto &[a0, a1, a2] = t;
    return f(a0, a1, a2);
  }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, uint64_t &, uint64_t &, uint64_t &>
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
  static std::optional<std::function<uint64_t(uint64_t)>>
  make_adder_from_triple(const triple &t);
  /// test1: MkTriple 10 20 30 -> base=60, go(5) = 60+5 = 65.
  static inline const uint64_t test1 = []() -> uint64_t {
    auto _cs = make_adder_from_triple(
        triple::mktriple(UINT64_C(10), UINT64_C(20), UINT64_C(30)));
    if (_cs.has_value()) {
      const std::function<uint64_t(uint64_t)> &f = *_cs;
      return f(UINT64_C(5));
    } else {
      return UINT64_C(999);
    }
  }();
  /// test2: With noise between creation and use.
  static inline const uint64_t test2 = []() {
    std::optional<std::function<uint64_t(uint64_t)>> o = make_adder_from_triple(
        triple::mktriple(UINT64_C(100), UINT64_C(200), UINT64_C(300)));
    uint64_t noise = (UINT64_C(42) + UINT64_C(13));
    if (o.has_value()) {
      const std::function<uint64_t(uint64_t)> &f = *o;
      return (f(UINT64_C(0)) + noise);
    } else {
      return UINT64_C(999);
    }
  }();
  /// Direct capture of pattern fields (no intermediate let binding).
  static std::optional<std::function<uint64_t(uint64_t)>>
  make_field_adder(const triple &t);

  /// test3: MkTriple 42 0 0 -> a=42, go(3) = 42+3 = 45.
  static inline const uint64_t test3 = []() -> uint64_t {
    auto _cs = make_field_adder(
        triple::mktriple(UINT64_C(42), UINT64_C(0), UINT64_C(0)));
    if (_cs.has_value()) {
      const std::function<uint64_t(uint64_t)> &f = *_cs;
      return f(UINT64_C(3));
    } else {
      return UINT64_C(999);
    }
  }();
};

#endif // INCLUDED_VALUE_TYPE_MATCH_FIX
