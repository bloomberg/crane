#ifndef INCLUDED_DEPENDENT_EXTRACTION_TARGETS_A
#define INCLUDED_DEPENDENT_EXTRACTION_TARGETS_A

#include <cstdint>
#include <dependent_extraction_targets_inner.h>
#include <type_traits>
#include <variant>

struct DependentExtractionTargets {
  struct A {
    struct t {
      // DATA
      uint64_t a0;

      // ACCESSORS
      t clone() const { return {a0}; }

      // CREATORS
      static t t0(uint64_t a0) { return {a0}; }
    };

    template <typename T1, typename F0>
      requires std::is_invocable_r_v<T1, F0 &, const uint64_t &>
    static T1 t_rect(F0 &&f, const t &t0) {
      const auto &[a0] = t0;
      return f(a0);
    }

    template <typename T1, typename F0> static T1 t_rec(F0 &&f, const t &t0) {
      return t_rect<T1>(f, t0);
    }

    static uint64_t get(const t &x);
  };
};

#endif // INCLUDED_DEPENDENT_EXTRACTION_TARGETS_A
