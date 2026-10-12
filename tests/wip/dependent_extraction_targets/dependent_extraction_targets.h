#ifndef INCLUDED_DEPENDENT_EXTRACTION_TARGETS
#define INCLUDED_DEPENDENT_EXTRACTION_TARGETS

#include <atomic>
#include <cstdint>
#include <dependent_extraction_targets_inner.h>
#include <type_traits>
#include <utility>
#include <variant>

struct DependentExtractionTargets {
  struct Inner {
    struct t {
      // TYPES
      struct A {};

      struct B {
        uint64_t a0;
      };

      using variant_t = std::variant<A, B>;

    private:
      // DATA
      variant_t v_;

    public:
      // CREATORS
      t() {}

      explicit t(A _v) : v_(_v) {}

      explicit t(B _v) : v_(std::move(_v)) {}

      static t a() { return t(A{}); }

      static t b(uint64_t a0) { return t(B{a0}); }

      // MANIPULATORS
      inline variant_t &v_mut() { return v_; }

      // ACCESSORS
      const variant_t &v() const { return v_; }
    };

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, const uint64_t &>
    static T1 t_rect(T1 f0, F1 &&f1, const t &t0) {
      if (std::holds_alternative<typename t::A>(t0.v())) {
        return f0;
      } else {
        const auto &[a0] = std::get<typename t::B>(t0.v());
        return f1(a0);
      }
    }

    template <typename T1, typename F1>
    static T1 t_rec(T1 f0, F1 &&f1, const t &t0) {
      return t_rect<T1>(std::move(f0), f1, t0);
    }

    static uint64_t f(const t &x);

    struct Deep {
      static inline const uint64_t g = f(t::b(UINT64_C(4)));
    };
  };

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
    static T1 t_rect(F0 &&f0, const t &t0) {
      const auto &[a0] = t0;
      return f0(a0);
    }

    template <typename T1, typename F0> static T1 t_rec(F0 &&f0, const t &t0) {
      return t_rect<T1>(f0, t0);
    }

    static uint64_t get(const t &x);
  };

  struct B {
    static inline const uint64_t use = A::get(A::t::t0(UINT64_C(9)));
  };

  template <typename T1> static List<T1> rep(const T1 &z, uint64_t n) {
    if (n <= 0) {
      return List<T1>::nil();
    } else {
      uint64_t m = n - 1;
      return List<T1>::cons(z, rep<T1>(z, m));
    }
  }

  static inline const uint64_t result =
      ((Inner::Deep::g + B::use) +
       length<uint64_t>(rep<uint64_t>(UINT64_C(7), UINT64_C(3))));
};

#endif // INCLUDED_DEPENDENT_EXTRACTION_TARGETS
