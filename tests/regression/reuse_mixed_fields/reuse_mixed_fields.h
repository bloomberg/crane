#ifndef INCLUDED_REUSE_MIXED_FIELDS
#define INCLUDED_REUSE_MIXED_FIELDS

#include <type_traits>
#include <utility>
#include <variant>

struct ReuseMixedFields {
  /// Two constructors with same arity but different field types.
  struct payload {
    // TYPES
    struct AsNat {
      uint64_t a0;
      uint64_t a1;
    };

    struct AsPair {
      uint64_t a0;
      uint64_t a1;
    };

    using variant_t = std::variant<AsNat, AsPair>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    payload() {}

    explicit payload(AsNat _v) : v_(std::move(_v)) {}

    explicit payload(AsPair _v) : v_(std::move(_v)) {}

    payload(const payload &_other) : v_(std::move(_other.clone().v_)) {}

    payload(payload &&_other) noexcept : v_(std::move(_other.v_)) {}

    payload &operator=(const payload &_other) {
      v_ = std::move(_other.clone().v_);
      return *this;
    }

    payload &operator=(payload &&_other) noexcept {
      v_ = std::move(_other.v_);
      return *this;
    }

    // ACCESSORS
    payload clone() const {
      if (std::holds_alternative<AsNat>(this->v())) {
        const auto &[a0, a1] = std::get<AsNat>(this->v());
        return payload(AsNat{a0, a1});
      } else {
        const auto &[a0, a1] = std::get<AsPair>(this->v());
        return payload(AsPair{a0, a1});
      }
    }

    // CREATORS
    static payload asnat(uint64_t a0, uint64_t a1) {
      return payload(AsNat{a0, a1});
    }

    static payload aspair(uint64_t a0, uint64_t a1) {
      return payload(AsPair{a0, a1});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename F0, typename F1>
    requires std::is_invocable_r_v<T1, F0 &, uint64_t &, uint64_t &> &&
             std::is_invocable_r_v<T1, F1 &, uint64_t &, uint64_t &>
  static T1 payload_rect(F0 &&f, F1 &&f0, const payload &p) {
    if (std::holds_alternative<typename payload::AsNat>(p.v())) {
      const auto &[a0, a1] = std::get<typename payload::AsNat>(p.v());
      return f(a0, a1);
    } else {
      const auto &[a0, a1] = std::get<typename payload::AsPair>(p.v());
      return f0(a0, a1);
    }
  }

  template <typename T1, typename F0, typename F1>
    requires std::is_invocable_r_v<T1, F0 &, uint64_t &, uint64_t &> &&
             std::is_invocable_r_v<T1, F1 &, uint64_t &, uint64_t &>
  static T1 payload_rec(F0 &&f, F1 &&f0, const payload &p) {
    if (std::holds_alternative<typename payload::AsNat>(p.v())) {
      const auto &[a0, a1] = std::get<typename payload::AsNat>(p.v());
      return f(a0, a1);
    } else {
      const auto &[a0, a1] = std::get<typename payload::AsPair>(p.v());
      return f0(a0, a1);
    }
  }

  /// Forces d to be owned through the else branch.
  /// The match branch has reuse candidates: both AsNat and AsPair
  /// have arity 2.
  static payload swap_tag_or_id(payload p, bool do_swap);
  /// test1: swap AsNat 10 20 -> should be AsPair 20 10.
  /// With reuse bug: variant stays AsNat, fields are 20, 10.
  /// Match sees AsNat -> returns first field + 1000 = 1020.
  /// Correct: Match sees AsPair -> returns first field = 20.
  static inline const uint64_t test1 = []() {
    auto &&_sv0 =
        swap_tag_or_id(payload::asnat(UINT64_C(10), UINT64_C(20)), true);
    if (std::holds_alternative<typename payload::AsNat>(_sv0.v())) {
      const auto &[a00, a10] = std::get<typename payload::AsNat>(_sv0.v());
      return (a00 + UINT64_C(1000));
    } else {
      const auto &[a00, a10] = std::get<typename payload::AsPair>(_sv0.v());
      return a00;
    }
  }();
  /// test2: chain two swaps. Should be identity.
  /// swap(swap(AsNat 5 6)) = swap(AsPair 6 5) = AsNat 5 6.
  /// With reuse bug: first swap returns AsNat 6 5 (wrong tag),
  /// second swap matches AsNat -> returns AsNat 5 6 (right tag but
  /// swapped fields).
  static inline const uint64_t test2 = []() {
    auto &&_sv1 = swap_tag_or_id(
        swap_tag_or_id(payload::asnat(UINT64_C(5), UINT64_C(6)), true), true);
    if (std::holds_alternative<typename payload::AsNat>(_sv1.v())) {
      const auto &[a01, a11] = std::get<typename payload::AsNat>(_sv1.v());
      return ((a01 * UINT64_C(10)) + a11);
    } else {
      const auto &[a01, a11] = std::get<typename payload::AsPair>(_sv1.v());
      return (((a01 * UINT64_C(10)) + a11) + UINT64_C(1000));
    }
  }();
};

#endif // INCLUDED_REUSE_MIXED_FIELDS
