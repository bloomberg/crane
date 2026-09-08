#ifndef INCLUDED_IMPORTED_MODULE_TYPE_PRIME
#define INCLUDED_IMPORTED_MODULE_TYPE_PRIME

#include <concepts>

template <typename M>
concept TotalLeBool_ = requires {
  typename M::t;
  {
    M::leb(std::declval<typename M::t>(), std::declval<typename M::t>())
  } -> std::same_as<bool>;
};

/// A module type declared in another library is re-emitted as a concept, but
/// its name is copied verbatim instead of being sanitised, so the apostrophe in
/// TotalLeBool' reaches the C++ output.  The reference in the functor's
/// template head is sanitised, to TotalLeBool_, so the two never agree.
struct ImportedModuleTypePrime {
  template <TotalLeBool_ X> struct F {
    static typename X::t pick(typename X::t a, typename X::t b) {
      if (X::leb(a, b)) {
        return a;
      } else {
        return b;
      }
    }
  };

  struct NatOrd {
    using t = uint64_t;
    static bool leb(uint64_t x0_, uint64_t x1_);
  };

  using FN = F<NatOrd>;
  static inline const uint64_t test = FN::pick(UINT64_C(3), UINT64_C(1));
};

#endif // INCLUDED_IMPORTED_MODULE_TYPE_PRIME
