#ifndef INCLUDED_CLASS_IN_NESTED_MODULE
#define INCLUDED_CLASS_IN_NESTED_MODULE

#include <concepts>
#include <utility>

/// A typeclass becomes a C++ concept, and a module becomes a struct.  A class
/// declared inside a module therefore emits a concept inside a struct, which
/// C++ allows only at namespace scope; every later reference to the class then
/// fails to resolve as well.
struct ClassInNestedModule {

  template <typename I, typename A>
  concept Show = requires {
    { I::sz(std::declval<A>()) } -> std::convertible_to<uint64_t>;
    { I::tag() } -> std::convertible_to<uint64_t>;
  };

  struct Cls {
    struct SN {
      static uint64_t sz(uint64_t x) { return x; }

      static uint64_t tag() { return UINT64_C(1); }
    };

    static_assert(Show<SN, uint64_t>);
  };

  template <typename _tcI0, typename T1>
    requires Cls::Show<_tcI0, T1>
  static uint64_t use(const T1 &x) {
    return (_tcI0::sz(x) + _tcI0::tag());
  }

  static inline const uint64_t run = use<Cls::SN, uint64_t>(UINT64_C(5));
};

#endif // INCLUDED_CLASS_IN_NESTED_MODULE
