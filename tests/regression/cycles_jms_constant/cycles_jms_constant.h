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

struct CyclesJmsConstant {
  struct instruction {
  public:
    struct JMS {
      unsigned int _a0;
    };
    struct NOP {};
    using variant_t = std::variant<JMS, NOP>;

  private:
    variant_t v_;
    explicit instruction(JMS _v) : v_(std::move(_v)) {}
    explicit instruction(NOP _v) : v_(std::move(_v)) {}

  public:
    struct ctor {
      ctor() = delete;
      static std::shared_ptr<instruction> JMS_(unsigned int a0) {
        return std::shared_ptr<instruction>(new instruction(JMS{a0}));
      }
      static std::shared_ptr<instruction> NOP_() {
        return std::shared_ptr<instruction>(new instruction(NOP{}));
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

  template <typename T1, MapsTo<T1, unsigned int> F0>
  static T1 instruction_rect(F0 &&f, const T1 f0,
                             const std::shared_ptr<instruction> &i) {
    return std::visit(
        Overloaded{
            [&](const typename instruction::JMS _args) -> T1 {
              unsigned int n = _args._a0;
              return f(std::move(n));
            },
            [&](const typename instruction::NOP _args) -> T1 { return f0; }},
        i->v());
  }

  template <typename T1, MapsTo<T1, unsigned int> F0>
  static T1 instruction_rec(F0 &&f, const T1 f0,
                            const std::shared_ptr<instruction> &i) {
    return std::visit(
        Overloaded{
            [&](const typename instruction::JMS _args) -> T1 {
              unsigned int n = _args._a0;
              return f(std::move(n));
            },
            [&](const typename instruction::NOP _args) -> T1 { return f0; }},
        i->v());
  }

  struct state {
    unsigned int acc;
  };

  static unsigned int acc(const std::shared_ptr<state> &s);

  static unsigned int cycles(const std::shared_ptr<state> &_x,
                             const std::shared_ptr<instruction> &i);

 static inline const unsigned int t = cycles(std::make_shared<state>(state{0}), instruction::ctor::JMS_((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1)));
};
