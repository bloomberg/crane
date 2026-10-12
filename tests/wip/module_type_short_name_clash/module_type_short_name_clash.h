#ifndef INCLUDED_MODULE_TYPE_SHORT_NAME_CLASH
#define INCLUDED_MODULE_TYPE_SHORT_NAME_CLASH

#include <concepts>
#include <cstdint>

template <typename M>
concept T = requires {
  requires(
      requires {
        { M::x } -> std::convertible_to<uint64_t>;
      } ||
      requires {
        { M::x() } -> std::convertible_to<uint64_t>;
      });
};
template <typename M>
concept T = requires {
  requires(
      requires {
        { M::y } -> std::convertible_to<bool>;
      } ||
      requires {
        { M::y() } -> std::convertible_to<bool>;
      });
};

struct ModuleTypeShortNameClash {
  struct A {
    template <T X> struct F {
      static const uint64_t &get() {
        static const uint64_t v = (X::x + UINT64_C(1));
        return v;
      }
    };
  };

  struct B {
    template <T X> struct F {
      static const uint64_t &get() {
        static const uint64_t v = (X::y ? UINT64_C(1) : UINT64_C(0));
        return v;
      }
    };
  };

  struct IA {
    static constexpr uint64_t x = UINT64_C(4);
  };

  struct IB {
    static constexpr bool y = true;
  };

  using FA = A::F<IA>;
  using FB = B::F<IB>;
  static inline const uint64_t result = (FA::get() + FB::get());
};

#endif // INCLUDED_MODULE_TYPE_SHORT_NAME_CLASH
