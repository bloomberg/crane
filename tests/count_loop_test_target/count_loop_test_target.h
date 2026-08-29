#ifndef INCLUDED_COUNT_LOOP_TEST_TARGET
#define INCLUDED_COUNT_LOOP_TEST_TARGET

#include <type_traits>
#include <utility>
#include <variant>

struct CountLoopTestTarget {
  struct instruction {
    // TYPES
    struct ISZ {
      uint64_t a0;
      uint64_t a1;
    };

    struct NOP {};

    using variant_t = std::variant<ISZ, NOP>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    instruction() {}

    explicit instruction(ISZ _v) : v_(std::move(_v)) {}

    explicit instruction(NOP _v) : v_(_v) {}

    static instruction isz(uint64_t a0, uint64_t a1) {
      return instruction(ISZ{a0, a1});
    }

    static instruction nop() { return instruction(NOP{}); }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, uint64_t &, uint64_t &>
  static T1 instruction_rect(F0 &&f, T1 f0, const instruction &i) {
    if (std::holds_alternative<typename instruction::ISZ>(i.v())) {
      const auto &[a0, a1] = std::get<typename instruction::ISZ>(i.v());
      return f(a0, a1);
    } else {
      return f0;
    }
  }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, uint64_t &, uint64_t &>
  static T1 instruction_rec(F0 &&f, T1 f0, const instruction &i) {
    if (std::holds_alternative<typename instruction::ISZ>(i.v())) {
      const auto &[a0, a1] = std::get<typename instruction::ISZ>(i.v());
      return f(a0, a1);
    } else {
      return f0;
    }
  }

  static instruction count_loop_test(uint64_t loop_addr);
  static uint64_t target_of(const instruction &i);
  static inline const uint64_t t = target_of(count_loop_test(UINT64_C(37)));
};

#endif // INCLUDED_COUNT_LOOP_TEST_TARGET
