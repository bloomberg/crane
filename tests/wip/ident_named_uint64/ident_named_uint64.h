#ifndef INCLUDED_IDENT_NAMED_UINT64
#define INCLUDED_IDENT_NAMED_UINT64

#include <type_traits>
#include <variant>

struct IdentNamedUint64 {
  struct t {
    // DATA
    uint64_t a0;

    // ACCESSORS
    t clone() const { return {a0}; }

    // CREATORS
    static t uint64_t_(uint64_t a0) { return {a0}; }
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

  static uint64_t uint64_t(uint64_t n);
  static inline const uint64_t go = (uint64_t(UINT64_C(1)) + UINT64_C(2));
};

#endif // INCLUDED_IDENT_NAMED_UINT64
