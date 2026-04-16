#ifndef INCLUDED_COUNT_LOOP_TEST_TARGET
#define INCLUDED_COUNT_LOOP_TEST_TARGET

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

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
    explicit instruction(ISZ _v) : d_v_(std::move(_v)) {}

    explicit instruction(NOP _v) : d_v_(_v) {}

    static std::shared_ptr<instruction> isz(unsigned int a0, unsigned int a1) {
      return std::make_shared<instruction>(ISZ{std::move(a0), std::move(a1)});
    }

    static std::shared_ptr<instruction> nop() {
      return std::make_shared<instruction>(NOP{});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, MapsTo<T1, unsigned int, unsigned int> F0>
  static T1 instruction_rect(F0 &&f, const T1 f0,
                             const std::shared_ptr<instruction> &i) {
    if (std::holds_alternative<typename instruction::ISZ>(i->v())) {
      const auto &[d_a0, d_a1] = std::get<typename instruction::ISZ>(i->v());
      return f(d_a0, d_a1);
    } else {
      return f0;
    }
  }

  template <typename T1, MapsTo<T1, unsigned int, unsigned int> F0>
  static T1 instruction_rec(F0 &&f, const T1 f0,
                            const std::shared_ptr<instruction> &i) {
    if (std::holds_alternative<typename instruction::ISZ>(i->v())) {
      const auto &[d_a0, d_a1] = std::get<typename instruction::ISZ>(i->v());
      return f(d_a0, d_a1);
    } else {
      return f0;
    }
  }

  static std::shared_ptr<instruction>
  count_loop_test(const unsigned int loop_addr);
  __attribute__((pure)) static unsigned int
  target_of(const std::shared_ptr<instruction> &i);
  static inline const unsigned int t = target_of(count_loop_test(37u));
};

#endif // INCLUDED_COUNT_LOOP_TEST_TARGET
