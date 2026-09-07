#ifndef INCLUDED_DICT_CTOR_FIELD
#define INCLUDED_DICT_CTOR_FIELD

#include <concepts>
#include <type_traits>
#include <utility>
#include <variant>

/// A type class becomes a C++ concept, so a constructor field whose Rocq type
/// is a class applied to a concrete type has no C++ type to be given.  Crane
/// writes the concept's name where a type belongs, producing
/// Sz a0; as a data member and passing the instance SzNat as a value.

template <typename I, typename A>
concept Sz = requires {
  { I::sz(std::declval<A>()) } -> std::convertible_to<uint64_t>;
};

struct DictCtorField {
  struct SzNat {
    static uint64_t sz(uint64_t n) { return n; }
  };

  static_assert(Sz<SzNat, uint64_t>);

  struct box {
    // DATA
    Sz<uint64_t> a0;
    uint64_t a1;

    // ACCESSORS
    box clone() const { return {a0, a1}; }

    // CREATORS
    static box box0(Sz<uint64_t> a0, uint64_t a1) {
      return {std::move(a0), a1};
    }
  };

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, Sz<uint64_t> &, uint64_t &>
  static T1 box_rect(F0 &&f, const box &b) {
    const auto &[a0, a1] = b;
    return f(a0, a1);
  }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, Sz<uint64_t> &, uint64_t &>
  static T1 box_rec(F0 &&f, const box &b) {
    const auto &[a0, a1] = b;
    return f(a0, a1);
  }

  static uint64_t run(const box &b);
  static inline const uint64_t test = run(box::box0(SzNat, UINT64_C(7)));
};

#endif // INCLUDED_DICT_CTOR_FIELD
