#ifndef INCLUDED_REUSE_TAG_MISMATCH
#define INCLUDED_REUSE_TAG_MISMATCH

#include <type_traits>
#include <utility>
#include <variant>

struct ReuseTagMismatch {
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

  static direction id_or_flip(direction d, bool flip_flag);
  static inline const uint64_t test1 =
      (std::holds_alternative<typename direction::GoUp>(
           id_or_flip(direction::goup(UINT64_C(42)), true).v())
           ? UINT64_C(1)
           : UINT64_C(2));
  static inline const uint64_t test2 =
      (std::holds_alternative<typename direction::GoUp>(
           id_or_flip(direction::goup(UINT64_C(42)), false).v())
           ? UINT64_C(1)
           : UINT64_C(2));
  static inline const uint64_t test3 =
      (std::holds_alternative<typename direction::GoUp>(
           id_or_flip(direction::godown(UINT64_C(100)), true).v())
           ? UINT64_C(3)
           : UINT64_C(4));
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
