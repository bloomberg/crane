#ifndef INCLUDED_COUNT_LOOP_TEST_TARGET
#define INCLUDED_COUNT_LOOP_TEST_TARGET

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

struct CountLoopTestTarget {
  struct instruction {
    // TYPES
    struct ISZ {
      unsigned int d_a0;
      unsigned int d_a1;
    };

    struct NOP {};

    using variant_t = std::variant<ISZ, NOP>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    instruction() {}

    explicit instruction(ISZ _v) : d_v_(std::move(_v)) {}

    explicit instruction(NOP _v) : d_v_(_v) {}

    instruction(const instruction &_other)
        : d_v_(std::move(_other.clone().d_v_)) {}

    instruction(instruction &&_other) : d_v_(std::move(_other.d_v_)) {}

    __attribute__((pure)) instruction &operator=(const instruction &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    __attribute__((pure)) instruction &operator=(instruction &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) instruction clone() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<ISZ>(_sv.v())) {
        const auto &[d_a0, d_a1] = std::get<ISZ>(_sv.v());
        return instruction(
            ISZ{[](auto &&__v) -> unsigned int {
                  if constexpr (
                      requires { __v ? 0 : 0; } && requires { *__v; } &&
                      requires { __v->clone(); } && requires { __v.get(); }) {
                    using _E = std::remove_cvref_t<decltype(*__v)>;
                    return __v ? std::make_unique<_E>(__v->clone()) : nullptr;
                  } else if constexpr (requires { __v.clone(); }) {
                    return __v.clone();
                  } else {
                    return __v;
                  }
                }(d_a0),
                [](auto &&__v) -> unsigned int {
                  if constexpr (
                      requires { __v ? 0 : 0; } && requires { *__v; } &&
                      requires { __v->clone(); } && requires { __v.get(); }) {
                    using _E = std::remove_cvref_t<decltype(*__v)>;
                    return __v ? std::make_unique<_E>(__v->clone()) : nullptr;
                  } else if constexpr (requires { __v.clone(); }) {
                    return __v.clone();
                  } else {
                    return __v;
                  }
                }(d_a1)});
      } else {
        return instruction(NOP{});
      }
    }

    // CREATORS
    __attribute__((pure)) static instruction isz(unsigned int a0,
                                                 unsigned int a1) {
      return instruction(ISZ{std::move(a0), std::move(a1)});
    }

    constexpr static instruction nop() { return instruction(NOP{}); }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) instruction *operator->() { return this; }

    __attribute__((pure)) const instruction *operator->() const { return this; }

    __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

    __attribute__((pure)) bool operator==(std::nullptr_t) const {
      return false;
    }

    // MANIPULATORS
    void reset() { *this = instruction(); }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, MapsTo<T1, unsigned int, unsigned int> F0>
  static T1 instruction_rect(F0 &&f, const T1 f0, const instruction &i) {
    if (std::holds_alternative<typename instruction::ISZ>(i.v())) {
      const auto &[d_a0, d_a1] = std::get<typename instruction::ISZ>(i.v());
      return f(d_a0, d_a1);
    } else {
      return f0;
    }
  }

  template <typename T1, MapsTo<T1, unsigned int, unsigned int> F0>
  static T1 instruction_rec(F0 &&f, const T1 f0, const instruction &i) {
    if (std::holds_alternative<typename instruction::ISZ>(i.v())) {
      const auto &[d_a0, d_a1] = std::get<typename instruction::ISZ>(i.v());
      return f(d_a0, d_a1);
    } else {
      return f0;
    }
  }

  __attribute__((pure)) static instruction
  count_loop_test(unsigned int loop_addr);
  __attribute__((pure)) static unsigned int target_of(const instruction &i);
  static inline const unsigned int t = target_of(count_loop_test(37u));
};

#endif // INCLUDED_COUNT_LOOP_TEST_TARGET
