#ifndef INCLUDED_NAME_CLASH_BINDING_REUSE
#define INCLUDED_NAME_CLASH_BINDING_REUSE

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

struct NameClashBindingReuse {
  /// Test: structured binding names (d_a0 etc.) reused across matches.
  /// Particularly tricky when matches are NOT wrapped in IIFEs
  /// (i.e. statement-position matches vs expression-position matches).
  struct pair_nat {
    // TYPES
    struct MkPairNat {
      unsigned int d_a0;
      unsigned int d_a1;
    };

    using variant_t = std::variant<MkPairNat>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    pair_nat() {}

    explicit pair_nat(MkPairNat _v) : d_v_(std::move(_v)) {}

    pair_nat(const pair_nat &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    pair_nat(pair_nat &&_other) : d_v_(std::move(_other.d_v_)) {}

    __attribute__((pure)) pair_nat &operator=(const pair_nat &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    __attribute__((pure)) pair_nat &operator=(pair_nat &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) pair_nat clone() const {
      auto &&_sv = *(this);
      const auto &[d_a0, d_a1] = std::get<MkPairNat>(_sv.v());
      return pair_nat(MkPairNat{d_a0, d_a1});
    }

    // CREATORS
    __attribute__((pure)) static pair_nat mkpairnat(unsigned int a0,
                                                    unsigned int a1) {
      return pair_nat(MkPairNat{std::move(a0), std::move(a1)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) pair_nat *operator->() { return this; }

    __attribute__((pure)) const pair_nat *operator->() const { return this; }

    __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

    __attribute__((pure)) bool operator==(std::nullptr_t) const {
      return false;
    }

    // MANIPULATORS
    void reset() { *this = pair_nat(); }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    /// Single-constructor match inside single-constructor match.
    /// Neither needs an if guard, just structured bindings.
    /// Could be tricky if both are in the same block without scoping.
    __attribute__((pure)) pair_nat flat_combine(const pair_nat &p2) const {
      auto &&_sv = *(this);
      const auto &[d_a0, d_a1] =
          std::get<typename pair_nat::MkPairNat>(_sv.v());
      const auto &[d_a00, d_a10] =
          std::get<typename pair_nat::MkPairNat>(p2.v());
      return pair_nat::mkpairnat((d_a0 + d_a00), (d_a1 + d_a10));
    }

    /// Same but as let-bindings (each match is an expression → IIFE).
    __attribute__((pure)) unsigned int add_pairs_let(const pair_nat &p2) const {
      unsigned int sum1 = [&]() {
        auto &&_sv = *(this);
        const auto &[d_a0, d_a1] =
            std::get<typename pair_nat::MkPairNat>(_sv.v());
        return (d_a0 + d_a1);
      }();
      unsigned int sum2 = [&]() {
        const auto &[d_a00, d_a10] =
            std::get<typename pair_nat::MkPairNat>(p2.v());
        return (d_a00 + d_a10);
      }();
      return (sum1 + sum2);
    }

    /// Two matches in sequence, both on pair_nat.
    /// Both generate d_a0, d_a1 structured bindings.
    __attribute__((pure)) unsigned int add_pairs(const pair_nat &p2) const {
      auto &&_sv = *(this);
      const auto &[d_a0, d_a1] =
          std::get<typename pair_nat::MkPairNat>(_sv.v());
      const auto &[d_a00, d_a10] =
          std::get<typename pair_nat::MkPairNat>(p2.v());
      return (((d_a0 + d_a1) + d_a00) + d_a10);
    }

    template <typename T1, MapsTo<T1, unsigned int, unsigned int> F0>
    T1 pair_nat_rec(F0 &&f) const {
      auto &&_sv = *(this);
      const auto &[d_a0, d_a1] =
          std::get<typename pair_nat::MkPairNat>(_sv.v());
      return f(d_a0, d_a1);
    }

    template <typename T1, MapsTo<T1, unsigned int, unsigned int> F0>
    T1 pair_nat_rect(F0 &&f) const {
      auto &&_sv = *(this);
      const auto &[d_a0, d_a1] =
          std::get<typename pair_nat::MkPairNat>(_sv.v());
      return f(d_a0, d_a1);
    }
  };

  struct triple_nat {
    // TYPES
    struct MkTripleNat {
      unsigned int d_a0;
      unsigned int d_a1;
      unsigned int d_a2;
    };

    using variant_t = std::variant<MkTripleNat>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    triple_nat() {}

    explicit triple_nat(MkTripleNat _v) : d_v_(std::move(_v)) {}

    triple_nat(const triple_nat &_other)
        : d_v_(std::move(_other.clone().d_v_)) {}

    triple_nat(triple_nat &&_other) : d_v_(std::move(_other.d_v_)) {}

    __attribute__((pure)) triple_nat &operator=(const triple_nat &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    __attribute__((pure)) triple_nat &operator=(triple_nat &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) triple_nat clone() const {
      auto &&_sv = *(this);
      const auto &[d_a0, d_a1, d_a2] = std::get<MkTripleNat>(_sv.v());
      return triple_nat(MkTripleNat{d_a0, d_a1, d_a2});
    }

    // CREATORS
    __attribute__((pure)) static triple_nat
    mktriplenat(unsigned int a0, unsigned int a1, unsigned int a2) {
      return triple_nat(
          MkTripleNat{std::move(a0), std::move(a1), std::move(a2)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) triple_nat *operator->() { return this; }

    __attribute__((pure)) const triple_nat *operator->() const { return this; }

    __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

    __attribute__((pure)) bool operator==(std::nullptr_t) const {
      return false;
    }

    // MANIPULATORS
    void reset() { *this = triple_nat(); }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    __attribute__((pure)) unsigned int cascade_and_match() const {
      auto &&_sv = (*(this)).cascade();
      const auto &[d_a0, d_a1] =
          std::get<typename pair_nat::MkPairNat>(_sv.v());
      return (d_a0 + d_a1);
    }

    /// Match where the binding variable is used as scrutinee of another match
    __attribute__((pure)) pair_nat cascade() const {
      auto &&_sv = *(this);
      const auto &[d_a0, d_a1, d_a2] =
          std::get<typename triple_nat::MkTripleNat>(_sv.v());
      return pair_nat::mkpairnat((d_a0 + d_a1), d_a2);
    }

    /// Nested match: outer match on triple, inner match on pair.
    /// Both have d_a0, d_a1; inner should get d_a00, d_a10.
    __attribute__((pure)) unsigned int combine(const pair_nat &p) const {
      auto &&_sv = *(this);
      const auto &[d_a0, d_a1, d_a2] =
          std::get<typename triple_nat::MkTripleNat>(_sv.v());
      const auto &[d_a00, d_a10] =
          std::get<typename pair_nat::MkPairNat>(p.v());
      return ((((d_a0 + d_a1) + d_a2) + d_a00) + d_a10);
    }

    template <typename T1,
              MapsTo<T1, unsigned int, unsigned int, unsigned int> F0>
    T1 triple_nat_rec(F0 &&f) const {
      auto &&_sv = *(this);
      const auto &[d_a0, d_a1, d_a2] =
          std::get<typename triple_nat::MkTripleNat>(_sv.v());
      return f(d_a0, d_a1, d_a2);
    }

    template <typename T1,
              MapsTo<T1, unsigned int, unsigned int, unsigned int> F0>
    T1 triple_nat_rect(F0 &&f) const {
      auto &&_sv = *(this);
      const auto &[d_a0, d_a1, d_a2] =
          std::get<typename triple_nat::MkTripleNat>(_sv.v());
      return f(d_a0, d_a1, d_a2);
    }
  };
};

#endif // INCLUDED_NAME_CLASH_BINDING_REUSE
