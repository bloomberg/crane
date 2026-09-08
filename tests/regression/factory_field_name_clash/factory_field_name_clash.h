#ifndef INCLUDED_FACTORY_FIELD_NAME_CLASH
#define INCLUDED_FACTORY_FIELD_NAME_CLASH

#include <type_traits>
#include <variant>

/// A constructor's factory method is named by lowercasing the constructor.  For
/// A : nat -> a that collides with the type name a, so it is renamed to
/// a0 -- which is exactly the default name given to the constructor's first
/// field.  The struct then declares uint64_t a0 and static a a0(uint64_t).
struct FactoryFieldNameClash {
  struct a {
    // DATA
    uint64_t a0_0;

    // ACCESSORS
    a clone() const { return {a0_0}; }

    // CREATORS
    static a a0(uint64_t a0_0) { return {a0_0}; }
  };

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, uint64_t &>
  static T1 a_rect(F0 &&f, const a &a0) {
    const auto &[a1] = a0;
    return f(a1);
  }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, uint64_t &>
  static T1 a_rec(F0 &&f, const a &a0) {
    const auto &[a1] = a0;
    return f(a1);
  }

  static uint64_t get(const a &x);
  static inline const uint64_t test = get(a::a0(UINT64_C(1)));
};

#endif // INCLUDED_FACTORY_FIELD_NAME_CLASH
