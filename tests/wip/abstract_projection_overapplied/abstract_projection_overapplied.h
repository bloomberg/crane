#ifndef INCLUDED_ABSTRACT_PROJECTION_OVERAPPLIED
#define INCLUDED_ABSTRACT_PROJECTION_OVERAPPLIED

#include "fn.h"
#include <concepts>
#include <cstdint>

template <typename M>
concept T = requires {
  typename M::alg;
  requires(
      requires {
        { M::a } -> std::convertible_to<typename M::alg>;
      } ||
      requires {
        { M::a() } -> std::convertible_to<typename M::alg>;
      });
};

struct AbstractProjectionOverapplied {
  struct Impl {
    struct alg {
      crane::fn<uint64_t(uint64_t)> step;
      uint64_t base;
    };

    static inline const alg a =
        alg{[](uint64_t x) { return (x + 1); }, UINT64_C(3)};
  };

  template <T X> struct Use {
    static const uint64_t &go() {
      static const uint64_t v = [](const auto &_x) {
        return _x.step;
      }(X::a, X::a.base);
      return v;
    }
  };

  using U = Use<Impl>;
  static inline const uint64_t result = U::go();
};

#endif // INCLUDED_ABSTRACT_PROJECTION_OVERAPPLIED
