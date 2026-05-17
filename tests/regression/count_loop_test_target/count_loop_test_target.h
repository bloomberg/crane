#ifndef INCLUDED_COUNT_LOOP_TEST_TARGET
#define INCLUDED_COUNT_LOOP_TEST_TARGET

#include <type_traits>
#include <utility>
#include <variant>

struct CountLoopTestTarget {
  struct instruction {
    // TYPES
    struct ISZ {
      unsigned int a0;
      unsigned int a1;
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

    instruction(const instruction &_other) : v_(std::move(_other.clone().v_)) {}

    instruction(instruction &&_other) noexcept : v_(std::move(_other.v_)) {}

    instruction &operator=(const instruction &_other) {
      v_ = std::move(_other.clone().v_);
      return *this;
    }

    instruction &operator=(instruction &&_other) noexcept {
      v_ = std::move(_other.v_);
      return *this;
    }

    // ACCESSORS
    instruction clone() const {
      if (std::holds_alternative<ISZ>(this->v())) {
        const auto &[a0, a1] = std::get<ISZ>(this->v());
        return instruction(ISZ{a0, a1});
      } else {
        return instruction(NOP{});
      }
    }

    // CREATORS
    static instruction isz(unsigned int a0, unsigned int a1) {
      return instruction(ISZ{a0, a1});
    }

    static instruction nop() { return instruction(NOP{}); }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, unsigned int &, unsigned int &>
  static T1 instruction_rect(F0 &&f, T1 f0, const instruction &i) {
    if (std::holds_alternative<typename instruction::ISZ>(i.v())) {
      const auto &[a0, a1] = std::get<typename instruction::ISZ>(i.v());
      return f(a0, a1);
    } else {
      return f0;
    }
  }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, unsigned int &, unsigned int &>
  static T1 instruction_rec(F0 &&f, T1 f0, const instruction &i) {
    if (std::holds_alternative<typename instruction::ISZ>(i.v())) {
      const auto &[a0, a1] = std::get<typename instruction::ISZ>(i.v());
      return f(a0, a1);
    } else {
      return f0;
    }
  }

  static instruction count_loop_test(unsigned int loop_addr);
  static unsigned int target_of(const instruction &i);
  static inline const unsigned int t = target_of(count_loop_test(37u));
};

#endif // INCLUDED_COUNT_LOOP_TEST_TARGET
