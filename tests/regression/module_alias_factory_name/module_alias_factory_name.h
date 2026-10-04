#ifndef INCLUDED_MODULE_ALIAS_FACTORY_NAME
#define INCLUDED_MODULE_ALIAS_FACTORY_NAME

#include <cstdint>
#include <type_traits>
#include <variant>

/// A module alias is transparent to Rocq but not to the factory-method namer:
/// reached through the alias A, the constructor c of Lib.t is called as
/// A::t::c0(...), while the type declares the factory as c.  Using Lib
/// directly works; only the aliased path gets the 0 suffix.
struct Lib {
  struct t {
    // DATA
    uint64_t a0;

    // ACCESSORS
    t clone() const { return {a0}; }

    // CREATORS
    static t c(uint64_t a0) { return {a0}; }
  };

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, const uint64_t &>
  static T1 t_rect(F0 &&f, const t &t0) {
    const auto &[a0] = t0;
    return f(a0);
  }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, const uint64_t &>
  static T1 t_rec(F0 &&f, const t &t0) {
    const auto &[a0] = t0;
    return f(a0);
  }

  static uint64_t get(const t &x);
};

using A = Lib;

struct ModuleAliasFactoryName {
  static inline const uint64_t run = A::get(A::t::c(UINT64_C(3)));
};

#endif // INCLUDED_MODULE_ALIAS_FACTORY_NAME
