#ifndef INCLUDED_MODULE_LOCAL_RETURN_TYPE
#define INCLUDED_MODULE_LOCAL_RETURN_TYPE

#include <type_traits>
#include <variant>

/// An out-of-line definition spells its return type *before* the qualified
/// function name, so the enclosing struct's scope is not yet open there.  A
/// function returning a type declared in a nested module is emitted as
/// M::t ModuleLocalReturnType::make(...), and M is undeclared at that
/// point.  Parameter types, which come after the qualified name, are fine.
struct ModuleLocalReturnType {
  struct M {
    struct t {
      // DATA
      uint64_t a0;

      // ACCESSORS
      t clone() const { return {a0}; }

      // CREATORS
      static t c(uint64_t a0) { return {a0}; }
    };

    template <typename T1, typename F0>
      requires std::is_invocable_r_v<T1, F0 &, uint64_t &>
    static T1 t_rect(F0 &&f, const t &t0) {
      const auto &[a0] = t0;
      return f(a0);
    }

    template <typename T1, typename F0>
      requires std::is_invocable_r_v<T1, F0 &, uint64_t &>
    static T1 t_rec(F0 &&f, const t &t0) {
      const auto &[a0] = t0;
      return f(a0);
    }
  };

  static M::t make(uint64_t n);
  static inline const uint64_t run = []() {
    const auto &_sv = make(UINT64_C(4));
    const auto &[a0] = _sv;
    return a0;
  }();
};

#endif // INCLUDED_MODULE_LOCAL_RETURN_TYPE
