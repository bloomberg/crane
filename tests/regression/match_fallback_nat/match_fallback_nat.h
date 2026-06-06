#ifndef INCLUDED_MATCH_FALLBACK_NAT
#define INCLUDED_MATCH_FALLBACK_NAT

#include <type_traits>
#include <utility>
#include <variant>

struct MatchFallbackNat {
  struct maybe_nat {
    // TYPES
    struct SomeNat {
      uint64_t a0;
    };

    struct NoneNat {};

    using variant_t = std::variant<SomeNat, NoneNat>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    maybe_nat() {}

    explicit maybe_nat(SomeNat _v) : v_(std::move(_v)) {}

    explicit maybe_nat(NoneNat _v) : v_(_v) {}

    static maybe_nat somenat(uint64_t a0) { return maybe_nat(SomeNat{a0}); }

    static maybe_nat nonenat() { return maybe_nat(NoneNat{}); }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, uint64_t &>
  static T1 maybe_nat_rect(F0 &&f, T1 f0, const maybe_nat &m) {
    if (std::holds_alternative<typename maybe_nat::SomeNat>(m.v())) {
      const auto &[a0] = std::get<typename maybe_nat::SomeNat>(m.v());
      return f(a0);
    } else {
      return f0;
    }
  }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, uint64_t &>
  static T1 maybe_nat_rec(F0 &&f, T1 f0, const maybe_nat &m) {
    if (std::holds_alternative<typename maybe_nat::SomeNat>(m.v())) {
      const auto &[a0] = std::get<typename maybe_nat::SomeNat>(m.v());
      return f(a0);
    } else {
      return f0;
    }
  }

  static uint64_t fallback(const maybe_nat &x);
  static inline const uint64_t t = (fallback(maybe_nat::nonenat()) +
                                    fallback(maybe_nat::somenat(UINT64_C(7))));
};

#endif // INCLUDED_MATCH_FALLBACK_NAT
