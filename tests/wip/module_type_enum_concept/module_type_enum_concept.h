#ifndef INCLUDED_MODULE_TYPE_ENUM_CONCEPT
#define INCLUDED_MODULE_TYPE_ENUM_CONCEPT

#include <cstdint>
#include <utility>

template <typename M>
concept T = requires { typename M::color; };

struct ModuleTypeEnumConcept {
  struct Impl {
    enum class Color { RED, GREEN };

    template <typename T1> static T1 color_rect(T1 f0, T1 f1, Color c) {
      switch (c) {
      case Color::RED: {
        return f0;
      }
      case Color::GREEN: {
        return f1;
      }
      default:
        std::unreachable();
      }
    }

    template <typename T1> static T1 color_rec(T1 f0, T1 f1, Color c) {
      return color_rect<T1>(std::move(f0), std::move(f1), c);
    }
  };

  template <T X> struct Use {
    constexpr static uint64_t f(X::Color c) {
      switch (c) {
      case X::Color::RED: {
        return UINT64_C(1);
      }
      case X::Color::GREEN: {
        return UINT64_C(2);
      }
      default:
        std::unreachable();
      }
    }
  };

  using U = Use<Impl>;
  static inline const uint64_t result = U::f(Impl::Color::GREEN);
};

#endif // INCLUDED_MODULE_TYPE_ENUM_CONCEPT
