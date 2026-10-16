#ifndef INCLUDED_PERSISTENT_ARRAY_DEFAULT_CONSTRUCTION
#define INCLUDED_PERSISTENT_ARRAY_DEFAULT_CONSTRUCTION

#include <cstdint>
#include <persistent_array.h>
#include <type_traits>
#include <utility>
#include <variant>

struct PersistentArrayDefaultConstruction {
  static inline const persistent_array<persistent_array<uint64_t>> grid =
      persistent_array<persistent_array<uint64_t>>(
          INT64_C(3), persistent_array<uint64_t>(INT64_C(3), UINT64_C(0)));
  static inline const persistent_array<persistent_array<uint64_t>> grid2 =
      grid.set(INT64_C(1), (grid.get(INT64_C(1))).set(INT64_C(1), UINT64_C(5)));
  static inline const uint64_t centre = (grid2.get(INT64_C(1))).get(INT64_C(1));

  struct t {
    // TYPES
    struct T0 {
      persistent_array<uint64_t> a0;
    };

    struct E {};

    using variant_t = std::variant<T0, E>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    t() {}

    explicit t(T0 _v) : v_(std::move(_v)) {}

    explicit t(E _v) : v_(_v) {}

    static t t0(persistent_array<uint64_t> a0) { return t(T0{std::move(a0)}); }

    static t e() { return t(E{}); }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, const persistent_array<uint64_t> &>
  static T1 t_rect(F0 &&f, T1 f0, const t &t0) {
    if (std::holds_alternative<typename t::T0>(t0.v())) {
      const auto &[a0] = std::get<typename t::T0>(t0.v());
      return f(a0);
    } else {
      return f0;
    }
  }

  template <typename T1, typename F0>
  static T1 t_rec(F0 &&f, T1 f0, const t &t0) {
    return t_rect<T1>(f, std::move(f0), t0);
  }

  static uint64_t get0(const t &x);
  static inline const uint64_t first =
      (get0(t::t0(persistent_array<uint64_t>(INT64_C(2), UINT64_C(7)))) +
       get0(t::e()));
};

#endif // INCLUDED_PERSISTENT_ARRAY_DEFAULT_CONSTRUCTION
