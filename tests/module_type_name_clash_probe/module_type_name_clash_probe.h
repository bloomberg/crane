#ifndef INCLUDED_MODULE_TYPE_NAME_CLASH_PROBE
#define INCLUDED_MODULE_TYPE_NAME_CLASH_PROBE

#include <type_traits>
#include <variant>

enum class Bool0 { TRUE_, FALSE_ };

struct ModuleTypeNameClashProbe {
  struct M_Mod {
    struct t {
      // DATA
      Bool0 a0;

      // ACCESSORS
      t clone() const { return {a0}; }

      // CREATORS
      static t t0(Bool0 a0) { return {a0}; }
    };

    template <typename T1, typename F0>
      requires std::is_invocable_r_v<T1, F0 &, Bool0 &>
    static T1 t_rect(F0 &&f, const t &t0) {
      const auto &[a0] = t0;
      return f(a0);
    }

    template <typename T1, typename F0>
      requires std::is_invocable_r_v<T1, F0 &, Bool0 &>
    static T1 t_rec(F0 &&f, const t &t0) {
      const auto &[a0] = t0;
      return f(a0);
    }
  };

  struct M {
    // DATA
    Bool0 a0;

    // ACCESSORS
    M clone() const { return {a0}; }

    // CREATORS
    static M mkm(Bool0 a0) { return {a0}; }
  };

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, Bool0 &>
  static T1 M_rect(F0 &&f, const M &m) {
    const auto &[a0] = m;
    return f(a0);
  }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, Bool0 &>
  static T1 M_rec(F0 &&f, const M &m) {
    const auto &[a0] = m;
    return f(a0);
  }

  static inline const Bool0 sample = Bool0::TRUE_;
};

#endif // INCLUDED_MODULE_TYPE_NAME_CLASH_PROBE
