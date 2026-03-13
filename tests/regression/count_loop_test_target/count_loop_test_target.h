#ifndef INCLUDED_COUNT_LOOP_TEST_TARGET
#define INCLUDED_COUNT_LOOP_TEST_TARGET

#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

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

    // CREATORS
    explicit instruction(ISZ _v) : d_v_(std::move(_v)) {}

    explicit instruction(NOP _v) : d_v_(std::move(_v)) {}

  public:
    // TYPES
    struct ctor {
      ctor() = delete;

      static std::shared_ptr<instruction> ISZ_(unsigned int a0,
                                               unsigned int a1) {
        return std::shared_ptr<instruction>(new instruction(ISZ{a0, a1}));
      }

      static std::shared_ptr<instruction> NOP_() {
        return std::shared_ptr<instruction>(new instruction(NOP{}));
      }

      static std::unique_ptr<instruction> ISZ_uptr(unsigned int a0,
                                                   unsigned int a1) {
        return std::unique_ptr<instruction>(new instruction(ISZ{a0, a1}));
      }

      static std::unique_ptr<instruction> NOP_uptr() {
        return std::unique_ptr<instruction>(new instruction(NOP{}));
      }
    };

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, MapsTo<T1, unsigned int, unsigned int> F0>
  static T1 instruction_rect(F0 &&f, const T1 f0,
                             const std::shared_ptr<instruction> &i) {
    return std::visit(
        Overloaded{
            [&](const typename instruction::ISZ _args) -> T1 {
              unsigned int n = _args.d_a0;
              unsigned int n0 = _args.d_a1;
              return f(std::move(n), std::move(n0));
            },
            [&](const typename instruction::NOP _args) -> T1 { return f0; }},
        i->v());
  }

  template <typename T1, MapsTo<T1, unsigned int, unsigned int> F0>
  static T1 instruction_rec(F0 &&f, const T1 f0,
                            const std::shared_ptr<instruction> &i) {
    return std::visit(
        Overloaded{
            [&](const typename instruction::ISZ _args) -> T1 {
              unsigned int n = _args.d_a0;
              unsigned int n0 = _args.d_a1;
              return f(std::move(n), std::move(n0));
            },
            [&](const typename instruction::NOP _args) -> T1 { return f0; }},
        i->v());
  }

  static std::shared_ptr<instruction>
  count_loop_test(const unsigned int loop_addr);
  __attribute__((pure)) static unsigned int
  target_of(const std::shared_ptr<instruction> &i);
  static inline const unsigned int t = target_of(count_loop_test(37u));
};

#endif // INCLUDED_COUNT_LOOP_TEST_TARGET
