#ifndef INCLUDED_DUPLICATE_CLASS_NAME_MODULES
#define INCLUDED_DUPLICATE_CLASS_NAME_MODULES

#include <concepts>
#include <cstdint>
#include <utility>

/// Two modules each declare a class called C.  A class is emitted as a
/// concept at file scope rather than inside its module's struct, so the second
/// one is a redefinition of the first.

template <typename I, typename A>
concept M1_C = requires {
  { I::m(std::declval<A>()) } -> std::convertible_to<uint64_t>;
};

struct M1 {
  struct i {
    static uint64_t m(uint64_t x) { return x; }
  };

  static_assert(M1_C<i, uint64_t>);
};

template <typename I, typename A>
concept M2_C = requires {
  { I::m(std::declval<A>()) } -> std::convertible_to<uint64_t>;
};

struct M2 {
  struct i {
    static uint64_t m(bool b) {
      if (b) {
        return UINT64_C(1);
      } else {
        return UINT64_C(0);
      }
    }
  };

  static_assert(M2_C<i, bool>);
};

struct DuplicateClassNameModules {
  static inline const uint64_t run = (M1::i::m(UINT64_C(1)) + M2::i::m(true));
};

#endif // INCLUDED_DUPLICATE_CLASS_NAME_MODULES
