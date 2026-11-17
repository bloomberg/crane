#ifndef INCLUDED_DEPENDENT_EXTRACTION_TARGETS_INNER
#define INCLUDED_DEPENDENT_EXTRACTION_TARGETS_INNER

#include <cstdint>
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
};

#endif // INCLUDED_DEPENDENT_EXTRACTION_TARGETS_INNER
