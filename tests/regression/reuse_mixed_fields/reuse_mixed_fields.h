#ifndef INCLUDED_REUSE_MIXED_FIELDS
#define INCLUDED_REUSE_MIXED_FIELDS

#include <memory>
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

template <typename T> struct is_shared_ptr : std::false_type {};

template <typename T>
struct is_shared_ptr<std::shared_ptr<T>> : std::true_type {
  using element_type = T;
};

template <typename T> struct is_optional : std::false_type {};

template <typename T> struct is_optional<std::optional<T>> : std::true_type {
  using element_type = T;
};

template <typename T> auto clone_value(const T &x) { return x; }

template <typename T>
std::unique_ptr<T> clone_value(const std::unique_ptr<T> &x) {
  return x ? std::make_unique<T>(x->clone()) : nullptr;
}

template <typename T>
std::shared_ptr<T> clone_value(const std::shared_ptr<T> &x) {
  if constexpr (requires { x->clone(); }) {
    return x ? std::make_shared<T>(x->clone()) : nullptr;
  } else {
    return x;
  }
}

template <typename Target, typename Source>
Target clone_as_value(const Source &x) {
  using TargetBare = std::remove_cvref_t<Target>;
  using SourceBare = std::remove_cvref_t<Source>;
  if constexpr (is_unique_ptr<TargetBare>::value) {
    using Inner = typename is_unique_ptr<TargetBare>::element_type;
    if constexpr (is_unique_ptr<SourceBare>::value) {
      using SourceInner = typename is_unique_ptr<SourceBare>::element_type;
      if (!x)
        return nullptr;
      if constexpr (std::is_same_v<Inner, SourceInner>) {
        return clone_value(x);
      } else if constexpr (requires {
                             typename Inner::crane_element_type;
                             x->template clone_as<
                                 typename Inner::crane_element_type>();
                           }) {
        return std::make_unique<Inner>(
            x->template clone_as<typename Inner::crane_element_type>());
      } else if constexpr (requires { x->template clone_as<Inner>(); }) {
        return std::make_unique<Inner>(x->template clone_as<Inner>());
      } else {
        return std::make_unique<Inner>(x->clone());
      }
    } else {
      if constexpr (requires { x.clone(); }) {
        return std::make_unique<Inner>(x.clone());
      } else if constexpr (std::is_same_v<Inner, SourceBare>) {
        if constexpr (requires { x.clone(); }) {
          return std::make_unique<Inner>(x.clone());
        } else {
          return std::make_unique<Inner>(x);
        }
      } else if constexpr (requires { x.template clone_as<Inner>(); }) {
        return std::make_unique<Inner>(x.template clone_as<Inner>());
      } else {
        if constexpr (requires { x.clone(); }) {
          return std::make_unique<Inner>(x.clone());
        } else {
          return std::make_unique<Inner>(x);
        }
      }
    }
  } else if constexpr (is_optional<TargetBare>::value) {
    using Inner = typename is_optional<TargetBare>::element_type;
    if constexpr (is_optional<SourceBare>::value) {
      if (!x)
        return std::nullopt;
      return Target{clone_as_value<Inner>(*x)};
    } else {
      return Target{clone_as_value<Inner>(x)};
    }
  } else if constexpr (is_shared_ptr<TargetBare>::value) {
    using Inner = typename is_shared_ptr<TargetBare>::element_type;
    if constexpr (is_shared_ptr<SourceBare>::value) {
      using SourceInner = typename is_shared_ptr<SourceBare>::element_type;
      if (!x)
        return nullptr;
      if constexpr (std::is_same_v<Inner, SourceInner>) {
        return clone_value(x);
      } else if constexpr (requires { x->template clone_as<Inner>(); }) {
        return std::make_shared<Inner>(x->template clone_as<Inner>());
      } else {
        return std::make_shared<Inner>(x->clone());
      }
    } else if constexpr (is_unique_ptr<SourceBare>::value) {
      if (!x)
        return nullptr;
      if constexpr (requires { x->template clone_as<Inner>(); }) {
        return std::make_shared<Inner>(x->template clone_as<Inner>());
      } else {
        return std::make_shared<Inner>(x->clone());
      }
    } else {
      if constexpr (std::is_same_v<Inner, SourceBare>) {
        return std::make_shared<Inner>(x.clone());
      } else if constexpr (requires { x.template clone_as<Inner>(); }) {
        return std::make_shared<Inner>(x.template clone_as<Inner>());
      } else {
        return std::make_shared<Inner>(x.clone());
      }
    }
  } else if constexpr (std::is_same_v<TargetBare, SourceBare>) {
    return clone_value(x);
  } else if constexpr (is_unique_ptr<SourceBare>::value) {
    using SourceInner = typename is_unique_ptr<SourceBare>::element_type;
    if constexpr (std::is_same_v<TargetBare, SourceInner>) {
      if (!x)
        return Target{};
      if constexpr (requires { x->clone(); }) {
        return x->clone();
      } else {
        return *x;
      }
    } else if constexpr (requires { x->template clone_as<TargetBare>(); }) {
      return x->template clone_as<TargetBare>();
    } else if constexpr (requires { x->clone(); }) {
      return x->clone();
    } else {
      return Target(*x);
    }
  } else if constexpr (is_shared_ptr<SourceBare>::value) {
    using SourceInner = typename is_shared_ptr<SourceBare>::element_type;
    if constexpr (std::is_same_v<TargetBare, SourceInner>) {
      return x ? x->clone() : Target{};
    } else if constexpr (requires { x->template clone_as<TargetBare>(); }) {
      return x->template clone_as<TargetBare>();
    } else {
      return Target(*x);
    }
  } else if constexpr (requires {
                         typename TargetBare::crane_element_type;
                         x.template clone_as<
                             typename TargetBare::crane_element_type>();
                       }) {
    return x.template clone_as<typename TargetBare::crane_element_type>();
  } else if constexpr (requires { x.template clone_as<TargetBare>(); }) {
    return x.template clone_as<TargetBare>();
  } else {
    return Target(x);
  }
}

struct ReuseMixedFields {
  /// Two constructors with same arity but different field types.
  struct payload {
    // TYPES
    struct AsNat {
      unsigned int d_a0;
      unsigned int d_a1;
    };

    struct AsPair {
      unsigned int d_a0;
      unsigned int d_a1;
    };

    using variant_t = std::variant<AsNat, AsPair>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    payload() {}

    explicit payload(AsNat _v) : d_v_(std::move(_v)) {}

    explicit payload(AsPair _v) : d_v_(std::move(_v)) {}

    payload(const payload &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    payload(payload &&_other) : d_v_(std::move(_other.d_v_)) {}

    __attribute__((pure)) payload &operator=(const payload &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    __attribute__((pure)) payload &operator=(payload &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) payload clone() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<AsNat>(_sv.v())) {
        const auto &[d_a0, d_a1] = std::get<AsNat>(_sv.v());
        return payload(AsNat{d_a0, d_a1});
      } else {
        const auto &[d_a0, d_a1] = std::get<AsPair>(_sv.v());
        return payload(AsPair{d_a0, d_a1});
      }
    }

    // CREATORS
    __attribute__((pure)) static payload asnat(unsigned int a0,
                                               unsigned int a1) {
      return payload(AsNat{std::move(a0), std::move(a1)});
    }

    __attribute__((pure)) static payload aspair(unsigned int a0,
                                                unsigned int a1) {
      return payload(AsPair{std::move(a0), std::move(a1)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) payload *operator->() { return this; }

    __attribute__((pure)) const payload *operator->() const { return this; }

    __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

    __attribute__((pure)) bool operator==(std::nullptr_t) const {
      return false;
    }

    // MANIPULATORS
    void reset() { *this = payload(); }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, MapsTo<T1, unsigned int, unsigned int> F0,
            MapsTo<T1, unsigned int, unsigned int> F1>
  static T1 payload_rect(F0 &&f, F1 &&f0, const payload &p) {
    if (std::holds_alternative<typename payload::AsNat>(p.v())) {
      const auto &[d_a0, d_a1] = std::get<typename payload::AsNat>(p.v());
      return f(d_a0, d_a1);
    } else {
      const auto &[d_a0, d_a1] = std::get<typename payload::AsPair>(p.v());
      return f0(d_a0, d_a1);
    }
  }

  template <typename T1, MapsTo<T1, unsigned int, unsigned int> F0,
            MapsTo<T1, unsigned int, unsigned int> F1>
  static T1 payload_rec(F0 &&f, F1 &&f0, const payload &p) {
    if (std::holds_alternative<typename payload::AsNat>(p.v())) {
      const auto &[d_a0, d_a1] = std::get<typename payload::AsNat>(p.v());
      return f(d_a0, d_a1);
    } else {
      const auto &[d_a0, d_a1] = std::get<typename payload::AsPair>(p.v());
      return f0(d_a0, d_a1);
    }
  }

  /// Forces d to be owned through the else branch.
  /// The match branch has reuse candidates: both AsNat and AsPair
  /// have arity 2.
  __attribute__((pure)) static payload swap_tag_or_id(payload p,
                                                      const bool &do_swap);
  /// test1: swap AsNat 10 20 -> should be AsPair 20 10.
  /// With reuse bug: variant stays AsNat, fields are 20, 10.
  /// Match sees AsNat -> returns first field + 1000 = 1020.
  /// Correct: Match sees AsPair -> returns first field = 20.
  static inline const unsigned int test1 = []() {
    auto &&_sv0 = swap_tag_or_id(payload::asnat(10u, 20u), true);
    if (std::holds_alternative<typename payload::AsNat>(_sv0.v())) {
      const auto &[d_a00, d_a10] = std::get<typename payload::AsNat>(_sv0.v());
      return (d_a00 + 1000u);
    } else {
      const auto &[d_a00, d_a10] = std::get<typename payload::AsPair>(_sv0.v());
      return d_a00;
    }
  }();
  /// test2: chain two swaps. Should be identity.
  /// swap(swap(AsNat 5 6)) = swap(AsPair 6 5) = AsNat 5 6.
  /// With reuse bug: first swap returns AsNat 6 5 (wrong tag),
  /// second swap matches AsNat -> returns AsNat 5 6 (right tag but
  /// swapped fields).
  static inline const unsigned int test2 = []() {
    auto &&_sv1 =
        swap_tag_or_id(swap_tag_or_id(payload::asnat(5u, 6u), true), true);
    if (std::holds_alternative<typename payload::AsNat>(_sv1.v())) {
      const auto &[d_a01, d_a11] = std::get<typename payload::AsNat>(_sv1.v());
      return ((d_a01 * 10u) + d_a11);
    } else {
      const auto &[d_a01, d_a11] = std::get<typename payload::AsPair>(_sv1.v());
      return (((d_a01 * 10u) + d_a11) + 1000u);
    }
  }();
};

#endif // INCLUDED_REUSE_MIXED_FIELDS
