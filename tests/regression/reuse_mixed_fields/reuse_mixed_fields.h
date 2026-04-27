#ifndef INCLUDED_REUSE_MIXED_FIELDS
#define INCLUDED_REUSE_MIXED_FIELDS

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

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

    payload &operator=(const payload &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    payload &operator=(payload &&_other) {
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
    inline variant_t &v_mut() { return d_v_; }

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
