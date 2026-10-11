#ifndef INCLUDED_MODULE_TYPE_ENUM_IN_PARAMETER
#define INCLUDED_MODULE_TYPE_ENUM_IN_PARAMETER

#include <concepts>
#include <cstdint>
#include <utility>

template <typename M>
concept T = requires {
  typename M::Color;
  typename M::t;
  {
    M::paint(std::declval<typename M::color>(), std::declval<typename M::t>())
  } -> std::same_as<typename M::t>;
  requires(
      requires {
        { M::base } -> std::convertible_to<typename M::t>;
      } ||
      requires {
        { M::base() } -> std::convertible_to<typename M::t>;
      });
};

struct ModuleTypeEnumInParameter {
  struct Impl {
    enum class Color { RED, GREEN, BLUE };

    template <typename T1> static T1 color_rect(T1 f, T1 f0, T1 f1, Color c) {
      switch (c) {
      case Color::RED: {
        return f;
      }
      case Color::GREEN: {
        return f0;
      }
      case Color::BLUE: {
        return f1;
      }
      default:
        std::unreachable();
      }
    }

    template <typename T1> static T1 color_rec(T1 f, T1 f0, T1 f1, Color c) {
      return color_rect<T1>(std::move(f), std::move(f0), std::move(f1), c);
    }

    using t = uint64_t;
    static t paint(Color c, uint64_t n);
    static inline const t base = UINT64_C(0);
  };

  template <T X> struct Use {
    static const typename X::t &go() {
      static const typename X::t v =
          X::paint(X::Color::BLUE, X::paint(X::Color::RED, X::base));
      return v;
    }
  };

  using U = Use<Impl>;
  static inline const uint64_t result = U::go();
};

#endif // INCLUDED_MODULE_TYPE_ENUM_IN_PARAMETER
