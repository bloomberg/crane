#ifndef INCLUDED_SIBLING_MODULE_TYPE_QUALIFIED
#define INCLUDED_SIBLING_MODULE_TYPE_QUALIFIED

#include <cstdint>
#include <variant>

/// A type defined in a sibling module is spelled relative to the extraction
/// target in the generated .cpp, not relative to the enclosing namespace:
/// the out-of-line definition of f says SiblingModuleTypeQualified::Lib::t
/// even though Lib is a sibling of the target, giving "no member named
/// 'Lib'".  The header, which spells the same type from inside the namespace,
/// is fine — only the .cpp disagrees.  Nesting the defining module deepens
/// the wrong prefix but does not change it.
struct Lib {
  struct t {
    // DATA
    uint64_t a0;

    // ACCESSORS
    t clone() const { return {a0}; }

    // CREATORS
    static t c(uint64_t a0) { return {a0}; }
  };

  struct Inner {
    struct u {
      // DATA
      uint64_t a0;

      // ACCESSORS
      u clone() const { return {a0}; }

      // CREATORS
      static u d(uint64_t a0) { return {a0}; }
    };
  };
};

struct SiblingModuleTypeQualified {
  static uint64_t f(const Lib::t &x);
  static uint64_t g(const Lib::Inner::u &y);
  static inline const uint64_t run =
      (f(Lib::t::c(UINT64_C(1))) + g(Lib::Inner::u::d(UINT64_C(2))));
};

#endif // INCLUDED_SIBLING_MODULE_TYPE_QUALIFIED
