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

struct JumpTargetSomeJms {
  struct instruction {
  public:
    struct JUN {
      unsigned int _a0;
    };
    struct JMS {
      unsigned int _a0;
    };
    struct NOP {};
    using variant_t = std::variant<JUN, JMS, NOP>;

  private:
    variant_t v_;
    explicit instruction(JUN _v) : v_(std::move(_v)) {}
    explicit instruction(JMS _v) : v_(std::move(_v)) {}
    explicit instruction(NOP _v) : v_(std::move(_v)) {}

  public:
    struct ctor {
      ctor() = delete;
      static std::shared_ptr<instruction> JUN_(unsigned int a0) {
        return std::shared_ptr<instruction>(new instruction(JUN{a0}));
      }
      static std::shared_ptr<instruction> JMS_(unsigned int a0) {
        return std::shared_ptr<instruction>(new instruction(JMS{a0}));
      }
      static std::shared_ptr<instruction> NOP_() {
        return std::shared_ptr<instruction>(new instruction(NOP{}));
      }
      static std::unique_ptr<instruction> JUN_uptr(unsigned int a0) {
        return std::unique_ptr<instruction>(new instruction(JUN{a0}));
      }
      static std::unique_ptr<instruction> JMS_uptr(unsigned int a0) {
        return std::unique_ptr<instruction>(new instruction(JMS{a0}));
      }
      static std::unique_ptr<instruction> NOP_uptr() {
        return std::unique_ptr<instruction>(new instruction(NOP{}));
      }
    };
    const variant_t &v() const { return v_; }
    variant_t &v_mut() { return v_; }
  };

  template <typename T1, MapsTo<T1, unsigned int> F0,
            MapsTo<T1, unsigned int> F1>
  static T1 instruction_rect(F0 &&f, F1 &&f0, const T1 f1,
                             const std::shared_ptr<instruction> &i) {
    return std::visit(
        Overloaded{
            [&](const typename instruction::JUN _args) -> T1 {
              unsigned int n = _args._a0;
              return f(std::move(n));
            },
            [&](const typename instruction::JMS _args) -> T1 {
              unsigned int n = _args._a0;
              return f0(std::move(n));
            },
            [&](const typename instruction::NOP _args) -> T1 { return f1; }},
        i->v());
  }

  template <typename T1, MapsTo<T1, unsigned int> F0,
            MapsTo<T1, unsigned int> F1>
  static T1 instruction_rec(F0 &&f, F1 &&f0, const T1 f1,
                            const std::shared_ptr<instruction> &i) {
    return std::visit(
        Overloaded{
            [&](const typename instruction::JUN _args) -> T1 {
              unsigned int n = _args._a0;
              return f(std::move(n));
            },
            [&](const typename instruction::JMS _args) -> T1 {
              unsigned int n = _args._a0;
              return f0(std::move(n));
            },
            [&](const typename instruction::NOP _args) -> T1 { return f1; }},
        i->v());
  }

  static std::optional<unsigned int>
  jump_target(const std::shared_ptr<instruction> &i);

  static unsigned int option_nat_or_zero(const std::optional<unsigned int> o);

 static inline const unsigned int t = option_nat_or_zero(jump_target(instruction::ctor::JMS_(((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1))));
};
