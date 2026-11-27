#pragma once

#include <concepts>
#include <cstdint>

struct Nat {
  static bool even(uint64_t n);
};

uint64_t dbl(uint64_t n);
inline constexpr uint64_t seven = UINT64_C(7);
template <typename M>
concept HasX = requires {
  requires (requires {
    {
      M::x
    }
    -> std::convertible_to<uint64_t>;
  } || requires {
    {
      M::x()
    }
    -> std::convertible_to<uint64_t>;
  });
};

struct ModuleAliasShadowsGlobal {
  /// Two levels down, naming the file-scope definitions, which the members
  /// of this module and of the enclosing one both hide.
  struct R {
    static uint64_t dbl(uint64_t x0_);
    static inline const uint64_t seven = ::seven;
  };

  /// A functor's struct, naming the file-scope definitions its members
  /// hide.
  template <HasX X> struct F {
    constexpr static uint64_t dbl(uint64_t x0_) { return ::dbl(x0_); }

    static const uint64_t &seven() {
      static const uint64_t v = ::seven;
      return v;
    }

    static const uint64_t &r() {
      static const uint64_t v = dbl(X::x + seven());
      return v;
    }
  };

  struct Three {
    static constexpr uint64_t x = UINT64_C(3);
  };

  using F3 = F<Three>;
  static uint64_t dbl(uint64_t x0_);
  static inline const uint64_t seven = ::seven;
  /// A definition of another file, which a collision wrapper holds.
  static bool even(uint64_t x0_);
  /// Uses the two aliases, which are now the members.
  static inline const uint64_t t = dbl(seven);

  /// Names the members of the enclosing module, which its own hide.
  struct Q {
    static uint64_t dbl(uint64_t n);
    static inline const uint64_t seven =
        ModuleAliasShadowsGlobal::seven + UINT64_C(1);
    static inline const uint64_t u = dbl(seven);
  };
};
