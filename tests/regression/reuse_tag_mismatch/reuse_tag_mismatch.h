#ifndef INCLUDED_REUSE_TAG_MISMATCH
#define INCLUDED_REUSE_TAG_MISMATCH

#include <type_traits>
#include <utility>
#include <variant>

struct ReuseTagMismatch {
  /// BUG HYPOTHESIS: The reuse optimization mutates variant fields in-place
  /// when use_count() == 1 and the tail constructor has the same arity
  /// as the matched constructor, even when they are DIFFERENT constructors.
  /// This leaves the variant with the WRONG tag — the original matched
  /// constructor tag persists instead of changing to the tail constructor.
  ///
  /// The reuse optimization fires when:
  /// 1. The scrutinee is "owned" (escapes in some code path)
  /// 2. The tail constructor has the same arity as the matched constructor
  /// 3. same_inductive holds (same type)
  /// 4. use_count() == 1 at runtime
  ///
  /// It does NOT check that matched_ctor == tail_ctor.
  struct direction {
    // TYPES
    struct GoUp {
      uint64_t a0;
    };

    struct GoDown {
      uint64_t a0;
    };

    using variant_t = std::variant<GoUp, GoDown>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    direction() {}

    explicit direction(GoUp _v) : v_(std::move(_v)) {}

    explicit direction(GoDown _v) : v_(std::move(_v)) {}

    direction(const direction &_other) : v_(std::move(_other.clone().v_)) {}

    direction(direction &&_other) noexcept : v_(std::move(_other.v_)) {}

    direction &operator=(const direction &_other) {
      v_ = std::move(_other.clone().v_);
      return *this;
    }

    direction &operator=(direction &&_other) noexcept {
      v_ = std::move(_other.v_);
      return *this;
    }

    // ACCESSORS
    direction clone() const {
      if (std::holds_alternative<GoUp>(this->v())) {
        const auto &[a0] = std::get<GoUp>(this->v());
        return direction(GoUp{a0});
      } else {
        const auto &[a0] = std::get<GoDown>(this->v());
        return direction(GoDown{a0});
      }
    }

    // CREATORS
    static direction goup(uint64_t a0) { return direction(GoUp{a0}); }

    static direction godown(uint64_t a0) { return direction(GoDown{a0}); }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename F0, typename F1>
    requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
             std::is_invocable_r_v<T1, F1 &, uint64_t &>
  static T1 direction_rect(F0 &&f, F1 &&f0, const direction &d) {
    if (std::holds_alternative<typename direction::GoUp>(d.v())) {
      const auto &[a0] = std::get<typename direction::GoUp>(d.v());
      return f(a0);
    } else {
      const auto &[a0] = std::get<typename direction::GoDown>(d.v());
      return f0(a0);
    }
  }

  template <typename T1, typename F0, typename F1>
    requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
             std::is_invocable_r_v<T1, F1 &, uint64_t &>
  static T1 direction_rec(F0 &&f, F1 &&f0, const direction &d) {
    if (std::holds_alternative<typename direction::GoUp>(d.v())) {
      const auto &[a0] = std::get<typename direction::GoUp>(d.v());
      return f(a0);
    } else {
      const auto &[a0] = std::get<typename direction::GoDown>(d.v());
      return f0(a0);
    }
  }

  /// The 'else d' branch causes d to escape (returned in tail position).
  /// This makes d "owned" (infer_owned_params marks it).
  /// The 'then' branch's match has reuse candidates because:
  /// - GoUp/GoDown are the same inductive (direction)
  /// - Both have arity 1
  /// But GoUp and GoDown are DIFFERENT constructors.
  static direction id_or_flip(direction d, bool flip_flag);
  /// test1: flip GoUp 42 -> should be GoDown 42.
  /// Match on the result:
  /// - GoUp _ => 1 (wrong, reuse bug would make this match)
  /// - GoDown _ => 2 (correct)
  static inline const uint64_t test1 =
      (std::holds_alternative<typename direction::GoUp>(
           id_or_flip(direction::goup(UINT64_C(42)), true).v())
           ? UINT64_C(1)
           : UINT64_C(2));
  /// test2: no flip -> should be GoUp 42 unchanged.
  static inline const uint64_t test2 =
      (std::holds_alternative<typename direction::GoUp>(
           id_or_flip(direction::goup(UINT64_C(42)), false).v())
           ? UINT64_C(1)
           : UINT64_C(2));
  /// test3: flip GoDown 100 -> should be GoUp 100.
  static inline const uint64_t test3 =
      (std::holds_alternative<typename direction::GoUp>(
           id_or_flip(direction::godown(UINT64_C(100)), true).v())
           ? UINT64_C(3)
           : UINT64_C(4));
  /// test4: use the flipped value's payload.
  static inline const uint64_t test4 = []() {
    auto &&_sv3 = id_or_flip(direction::goup(UINT64_C(10)), true);
    if (std::holds_alternative<typename direction::GoUp>(_sv3.v())) {
      const auto &[a03] = std::get<typename direction::GoUp>(_sv3.v());
      return (a03 + UINT64_C(1000));
    } else {
      const auto &[a03] = std::get<typename direction::GoDown>(_sv3.v());
      return a03;
    }
  }();
};

#endif // INCLUDED_REUSE_TAG_MISMATCH
