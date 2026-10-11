#ifndef INCLUDED_TYPE_FAMILY_CONSTANT_MOTIVE
#define INCLUDED_TYPE_FAMILY_CONSTANT_MOTIVE

#include "obj.h"
#include <algorithm>
#include <cstdint>
#include <type_traits>
#include <utility>

enum class Comparison;
enum class CompareSpecT;
enum class Comparison { EQ, LT, GT };
enum class CompareSpecT { COMPEQT, COMPLTT, COMPGTT };
template <typename a = void> using CompSpecT = CompareSpecT;

struct Datatypes {
  static CompareSpecT CompareSpec2Type(Comparison c);
  template <typename T1>
  static CompSpecT<T1> CompSpec2Type(const T1 &_x, const T1 &_x0,
                                     Comparison x0_);
};

struct Nat {
  static Comparison compare(uint64_t n, uint64_t m);

  struct Private_Dec {
    template <typename T1, typename F2>
      requires std::is_invocable_r_v<T1, F2 &, uint64_t &, uint64_t, const T1 &>
    static T1 max_case_strong(uint64_t n, uint64_t m, F2 &&compat, const T1 &hl,
                              const T1 &hr) {
      CompareSpecT c = Datatypes::CompSpec2Type(n, m, compare(n, m));
      switch (c) {
      case CompareSpecT::COMPGTT: {
        return compat(n, std::max(n, m), hl);
      }
      default: {
        return compat(m, std::max(n, m), hr);
      }
      }
    }

    template <typename T1, typename F2>
    static T1 max_case(uint64_t n, uint64_t m, F2 &&x, const T1 &x0,
                       const T1 &x1) {
      return max_case_strong<T1>(
          n, m, x, [=]() { return x0; }(), [=]() { return x1; }());
    }

    static bool max_dec(uint64_t n, uint64_t m);
  };

  static bool max_dec(uint64_t x0_, uint64_t x1_);
};

struct TypeFamilyConstantMotive {
  template <typename T1, typename F2>
  static T1 pick(uint64_t n, uint64_t m, F2 &&compat, const T1 &hl,
                 const T1 &hr) {
    if (m <= n) {
      return compat(n, std::max(n, m), hl);
    } else {
      return compat(m, std::max(n, m), hr);
    }
  }

  static bool larger_is_first(uint64_t n, uint64_t m);
  static inline const bool first = larger_is_first(UINT64_C(5), UINT64_C(3));
  /// The same shape in the standard library.
  static inline const bool max_is_left =
      (Nat::max_dec(UINT64_C(5), UINT64_C(3)) ? true : false);
};

template <typename T1>
CompSpecT<T1> Datatypes::CompSpec2Type(const T1 &, const T1 &, Comparison x0_) {
  return Datatypes::CompareSpec2Type(x0_);
}

#endif // INCLUDED_TYPE_FAMILY_CONSTANT_MOTIVE
