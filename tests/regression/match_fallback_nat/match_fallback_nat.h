#ifndef INCLUDED_MATCH_FALLBACK_NAT
#define INCLUDED_MATCH_FALLBACK_NAT

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

template <typename T> struct is_unique_ptr : std::false_type {};

template <typename T>
struct is_unique_ptr<std::unique_ptr<T>> : std::true_type {
  using element_type = T;
};

template <typename T> auto clone_value(const T &x) { return x; }

template <typename T>
std::unique_ptr<T> clone_value(const std::unique_ptr<T> &x) {
  if constexpr (requires { x->clone(); }) {
    return x ? std::make_unique<T>(x->clone()) : nullptr;
  } else {
    return x ? std::make_unique<T>(*x) : nullptr;
  }
}

template <typename Target, typename Source>
Target clone_as_value(const Source &x) {
  using T = std::remove_cvref_t<Target>;
  using S = std::remove_cvref_t<Source>;
  if constexpr (requires(const S &s) {
                  s.has_value();
                  *s;
                }) {
    if (!x.has_value())
      return T{};
    using TInner = std::remove_cvref_t<decltype(*std::declval<const T &>())>;
    return T{clone_as_value<TInner>(*x)};
  } else if constexpr (std::is_same_v<T, S>) {
    if constexpr (is_unique_ptr<T>::value) {
      return clone_value(x);
    } else if constexpr (requires { x.clone(); }) {
      return x.clone();
    } else {
      return x;
    }
  } else if constexpr (is_unique_ptr<S>::value) {
    if (!x)
      return T{};
    return clone_as_value<T>(*x);
  } else if constexpr (is_unique_ptr<T>::value) {
    using Inner = typename is_unique_ptr<T>::element_type;
    return std::make_unique<Inner>(clone_as_value<Inner>(x));
  } else {
    return T(x);
  }
}

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

    __attribute__((pure)) maybe_nat &operator=(const maybe_nat &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    __attribute__((pure)) maybe_nat &operator=(maybe_nat &&_other) {
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
