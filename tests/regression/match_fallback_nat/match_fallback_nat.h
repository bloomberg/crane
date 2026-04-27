#ifndef INCLUDED_MATCH_FALLBACK_NAT
#define INCLUDED_MATCH_FALLBACK_NAT

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

struct MatchFallbackNat {
  struct maybe_nat {
    // TYPES
    struct SomeNat {
      unsigned int d_a0;
    };

    struct NoneNat {};

    using variant_t = std::variant<SomeNat, NoneNat>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    maybe_nat() {}

    explicit maybe_nat(SomeNat _v) : d_v_(std::move(_v)) {}

    explicit maybe_nat(NoneNat _v) : d_v_(_v) {}

    maybe_nat(const maybe_nat &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    maybe_nat(maybe_nat &&_other) : d_v_(std::move(_other.d_v_)) {}

    maybe_nat &operator=(const maybe_nat &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    maybe_nat &operator=(maybe_nat &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) maybe_nat clone() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<SomeNat>(_sv.v())) {
        const auto &[d_a0] = std::get<SomeNat>(_sv.v());
        return maybe_nat(SomeNat{d_a0});
      } else {
        return maybe_nat(NoneNat{});
      }
    }

    // CREATORS
    __attribute__((pure)) static maybe_nat somenat(unsigned int a0) {
      return maybe_nat(SomeNat{std::move(a0)});
    }

    constexpr static maybe_nat nonenat() { return maybe_nat(NoneNat{}); }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) maybe_nat *operator->() { return this; }

    __attribute__((pure)) const maybe_nat *operator->() const { return this; }

    __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

    __attribute__((pure)) bool operator==(std::nullptr_t) const {
      return false;
    }

    // MANIPULATORS
    void reset() { *this = maybe_nat(); }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, MapsTo<T1, unsigned int> F0>
  static T1 maybe_nat_rect(F0 &&f, const T1 f0, const maybe_nat &m) {
    if (std::holds_alternative<typename maybe_nat::SomeNat>(m.v())) {
      const auto &[d_a0] = std::get<typename maybe_nat::SomeNat>(m.v());
      return f(d_a0);
    } else {
      return f0;
    }
  }

  template <typename T1, MapsTo<T1, unsigned int> F0>
  static T1 maybe_nat_rec(F0 &&f, const T1 f0, const maybe_nat &m) {
    if (std::holds_alternative<typename maybe_nat::SomeNat>(m.v())) {
      const auto &[d_a0] = std::get<typename maybe_nat::SomeNat>(m.v());
      return f(d_a0);
    } else {
      return f0;
    }
  }

  __attribute__((pure)) static unsigned int fallback(const maybe_nat &x);
  static inline const unsigned int t =
      (fallback(maybe_nat::nonenat()) + fallback(maybe_nat::somenat(7u)));
};

#endif // INCLUDED_MATCH_FALLBACK_NAT
