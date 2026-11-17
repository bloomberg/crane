#ifndef INCLUDED_FUNCTOR_LOCAL_CLASS_TEMPLATE_KW
#define INCLUDED_FUNCTOR_LOCAL_CLASS_TEMPLATE_KW

#include <concepts>
#include <cstdint>

/// A class declared inside a functor is reached, after instantiation, through
/// a template disambiguator that does not belong there: the generated code
/// says FN::template use(...) for a plain member, and clang answers "'use'
/// following the 'template' keyword does not refer to a template".
template <typename M>
concept S = requires {
  typename M::t;
  requires (requires {
    {
      M::z
    }
    -> std::convertible_to<typename M::t>;
  } || requires {
    {
      M::z()
    }
    -> std::convertible_to<typename M::t>;
  });
};

template <S X> struct F {
  struct Cl {
    typename X::t get;
  };

  static const Cl &inst() {
    static const Cl v = Cl{X::z};
    return v;
  }

  static typename X::t use(const Cl &c) { return c.get; }
};

struct N {
  using t = uint64_t;
  static constexpr uint64_t z = UINT64_C(0);
};

using FN = F<N>;

struct FunctorLocalClassTemplateKw {
  static inline const uint64_t run = FN::use(FN::inst());
};

#endif // INCLUDED_FUNCTOR_LOCAL_CLASS_TEMPLATE_KW
