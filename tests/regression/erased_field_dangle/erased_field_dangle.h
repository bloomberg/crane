#ifndef INCLUDED_ERASED_FIELD_DANGLE
#define INCLUDED_ERASED_FIELD_DANGLE

#include "crane_fn.h"
#include "fn.h"
#include "obj.h"
#include <any>
#include <utility>
#include <variant>

/// Memory safety probe: type-indexed inductives and erased fields.
///
/// When an inductive is indexed by a type (not parameterized), Crane
/// erases the index to std::any. Accessing fields stored as std::any
/// requires any_cast, which creates a temporary. If a reference to
/// the any_cast result is used after the temporary dies, we get UB.
///
/// This probes patterns where:
/// 1. A type-indexed container stores values as std::any
/// 2. Pattern matching extracts the any value
/// 3. The extracted value is used in a context where its lifetime
/// may have ended
struct ErasedFieldDangle {
  /// A container indexed by the element type — not parameterized.
  /// The index is erased to std::any in C++.
  struct box {
    // DATA
    crane::obj a;

    // ACCESSORS
    box clone() const { return {a}; }

    // CREATORS
    static box mkbox(crane::obj a) { return {std::move(a)}; }

    /// Extract the value from a box. In Rocq this is safe.
    /// In C++, the any_cast result is a temporary.
    template <typename T1> T1 unbox() const {
      const auto &[a] = *this;
      return crane_any_cast<T1>(a);
    }

    template <typename T2, typename F0> crane::obj box_rec(F0 &&f) const {
      const auto &[a0] = *this;
      return crane_call_erased(f, crane_any_cast<T2>(a0));
    }

    template <typename T2, typename F0> crane::obj box_rect(F0 &&f) const {
      const auto &[a0] = *this;
      return crane_call_erased(f, crane_any_cast<T2>(a0));
    }
  };

  /// Nested boxes: box of box
  static inline const box nested_box =
      box::mkbox(std::make_pair(UINT64_C(42), UINT64_C(58)));
  static inline const uint64_t test_unbox_nested = []() {
    std::pair<uint64_t, uint64_t> p =
        nested_box.template unbox<std::pair<uint64_t, uint64_t>>();
    return (p.first + p.second);
  }();
  /// Use unboxed value in a computation
  static inline const uint64_t test_unbox_compute = []() {
    uint64_t x = box::mkbox(UINT64_C(10)).template unbox<uint64_t>();
    uint64_t y = box::mkbox(UINT64_C(20)).template unbox<uint64_t>();
    return (x + y);
  }();
  /// Chain unbox through multiple let bindings
  static inline const uint64_t test_chain_unbox = []() {
    box b1 = box::mkbox(UINT64_C(5));
    box b2 = box::mkbox(
        (crane::any_cast<uint64_t>(std::move(b1).template unbox<uint64_t>()) +
         UINT64_C(10)));
    box b3 = box::mkbox(
        (crane::any_cast<uint64_t>(std::move(b2).template unbox<uint64_t>()) +
         UINT64_C(20)));
    return std::move(b3).template unbox<uint64_t>();
  }();
  /// Pass unboxed value to a higher-order function
  static inline const uint64_t test_hof_unbox = []() {
    box b = box::mkbox(crane::fn<uint64_t(uint64_t)>(
        [](uint64_t x) { return (x * UINT64_C(2)); }));
    return std::move(b).template unbox<crane::fn<uint64_t(uint64_t)>>()(
        UINT64_C(21));
  }();

  /// Existential container: hide the type
  struct exists_box {
    // DATA
    crane::obj a;
    crane::fn<uint64_t(crane::obj)> a1;

    // ACCESSORS
    exists_box clone() const { return {a, a1}; }

    // CREATORS
    static exists_box pack(crane::obj a, crane::fn<uint64_t(crane::obj)> a1) {
      return {std::move(a), std::move(a1)};
    }

    uint64_t run_exists() const {
      const auto &[a, a1] = *this;
      return a1(a);
    }

    template <typename T1, typename F0> T1 exists_box_rec(F0 &&f) const {
      const auto &[a0, a1] = *this;
      return f(a0, a1);
    }

    template <typename T1, typename F0> T1 exists_box_rect(F0 &&f) const {
      const auto &[a0, a1] = *this;
      return f(a0, a1);
    }
  };

  static inline const uint64_t test_exists = []() {
    exists_box e = exists_box::pack(
        UINT64_C(7),
        crane::fn<uint64_t(crane::obj)>([](const crane::obj &x) -> uint64_t {
          return (crane::any_cast<uint64_t>(x) * crane::any_cast<uint64_t>(x));
        }));
    return std::move(e).run_exists();
  }();
};

#endif // INCLUDED_ERASED_FIELD_DANGLE
