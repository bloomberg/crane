#ifndef INCLUDED_CTOR_FIELD_SHADOWS_TYPE
#define INCLUDED_CTOR_FIELD_SHADOWS_TYPE

#include <cstdint>
#include <type_traits>
#include <variant>

struct CtorFieldShadowsType {
  struct t {
    // DATA
    uint64_t t_0;
    uint64_t extra;

    // ACCESSORS
    t clone() const { return {t_0, extra}; }

    // CREATORS
    static t mk(uint64_t t_0, uint64_t extra) { return {t_0, extra}; }
  };

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, const uint64_t &, const uint64_t &>
  static T1 t_rect(F0 &&f, const t &t0) {
    const auto &[t_0, extra0] = t0;
    return f(t_0, extra0);
  }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, const uint64_t &, const uint64_t &>
  static T1 t_rec(F0 &&f, const t &t0) {
    const auto &[t_0, extra0] = t0;
    return f(t_0, extra0);
  }

  static uint64_t total(const t &x);
  static inline const uint64_t answer = total(t::mk(UINT64_C(1), UINT64_C(2)));
};

#endif // INCLUDED_CTOR_FIELD_SHADOWS_TYPE
