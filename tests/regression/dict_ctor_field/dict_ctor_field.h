#ifndef INCLUDED_DICT_CTOR_FIELD
#define INCLUDED_DICT_CTOR_FIELD

#include "crane_fn.h"
#include "fn.h"
#include <cstdint>
#include <type_traits>
#include <utility>
#include <variant>

/// A type class becomes a C++ concept, so a constructor field whose Rocq type
/// is a class applied to a concrete type has no C++ type to be given.  Crane
/// writes the concept's name where a type belongs, producing
/// Sz a0; as a data member and passing the instance SzNat as a value.
struct DictCtorField {
  template <typename A> struct Sz {
    crane::fn<uint64_t(A)> sz;

    // ACCESSORS
    template <typename CraneU> operator Sz<CraneU>() const {
      return {crane_convert<crane::fn<uint64_t(CraneU)>>(sz)};
    }
  };

  static inline const Sz<uint64_t> SzNat =
      Sz<uint64_t>{[](uint64_t n) { return n; }};

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
    requires std::is_invocable_r_v<T1, F0 &, const Sz<uint64_t> &,
                                   const uint64_t &>
  static T1 box_rect(F0 &&f, const box &b) {
    const auto &[a0, a1] = b;
    return f(a0, a1);
  }

  template <typename T1, typename F0> static T1 box_rec(F0 &&f, const box &b) {
    return box_rect<T1>(f, b);
  }

  static uint64_t run(const box &b);
  static constexpr uint64_t test = UINT64_C(7);
};

#endif // INCLUDED_DICT_CTOR_FIELD
