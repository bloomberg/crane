#ifndef INCLUDED_MODULE_ALIAS_VALUE_BESIDE_ACCESSOR
#define INCLUDED_MODULE_ALIAS_VALUE_BESIDE_ACCESSOR

#include <concepts>
#include <cstdint>

template <typename M>
concept T = requires {
  typename M::t;
  requires(
      requires {
        { M::z } -> std::convertible_to<typename M::t>;
      } ||
      requires {
        { M::z() } -> std::convertible_to<typename M::t>;
      });
};

struct ModuleAliasValueBesideAccessor {
  struct Outer {
    struct Inner {
      using t = uint64_t;
      static constexpr uint64_t z = UINT64_C(1);
    };

    template <T X> struct P {
      using t = typename X::t;

      static const typename X::t &z() {
        static const typename X::t v = [] {
          if constexpr (requires { X::z(); })
            return X::z();
          else
            return X::z;
        }();
        return v;
      }
    };
  };

  template <T X> struct F {
    using I = typename Outer::Inner;

    static const uint64_t &get() {
      static const uint64_t v = I::z;
      return v;
    }
  };

  using FN = F<Outer::Inner>;
  using PN = Outer::P<Outer::Inner>;
  static inline const uint64_t from_alias = FN::get();
  static inline const uint64_t from_accessor = PN::z();
};

#endif // INCLUDED_MODULE_ALIAS_VALUE_BESIDE_ACCESSOR
