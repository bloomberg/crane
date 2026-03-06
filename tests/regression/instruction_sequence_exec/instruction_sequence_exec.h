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

template <typename A> struct List {
public:
  struct nil {};
  struct cons {
    A _a0;
    std::shared_ptr<List<A>> _a1;
  };
  using variant_t = std::variant<nil, cons>;

private:
  variant_t v_;
  explicit List(nil _v) : v_(std::move(_v)) {}
  explicit List(cons _v) : v_(std::move(_v)) {}

public:
  struct ctor {
    ctor() = delete;
    static std::shared_ptr<List<A>> nil_() {
      return std::shared_ptr<List<A>>(new List<A>(nil{}));
    }
    static std::shared_ptr<List<A>> cons_(A a0,
                                          const std::shared_ptr<List<A>> &a1) {
      return std::shared_ptr<List<A>>(new List<A>(cons{a0, a1}));
    }
    static std::unique_ptr<List<A>> nil_uptr() {
      return std::unique_ptr<List<A>>(new List<A>(nil{}));
    }
    static std::unique_ptr<List<A>>
    cons_uptr(A a0, const std::shared_ptr<List<A>> &a1) {
      return std::unique_ptr<List<A>>(new List<A>(cons{a0, a1}));
    }
  };
  const variant_t &v() const { return v_; }
  variant_t &v_mut() { return v_; }
};

struct InstructionSequenceExec {
  struct state {
    unsigned int pc_;
    unsigned int acc_;
  };

  static unsigned int pc_(const std::shared_ptr<state> &s);

  static unsigned int acc_(const std::shared_ptr<state> &s);

  struct instruction {
  public:
    struct NOP_ {};
    struct INC_PC {};
    struct ADD_ACC {
      unsigned int _a0;
    };
    using variant_t = std::variant<NOP_, INC_PC, ADD_ACC>;

  private:
    variant_t v_;
    explicit instruction(NOP_ _v) : v_(std::move(_v)) {}
    explicit instruction(INC_PC _v) : v_(std::move(_v)) {}
    explicit instruction(ADD_ACC _v) : v_(std::move(_v)) {}

  public:
    struct ctor {
      ctor() = delete;
      static std::shared_ptr<instruction> NOP__() {
        return std::shared_ptr<instruction>(new instruction(NOP_{}));
      }
      static std::shared_ptr<instruction> INC_PC_() {
        return std::shared_ptr<instruction>(new instruction(INC_PC{}));
      }
      static std::shared_ptr<instruction> ADD_ACC_(unsigned int a0) {
        return std::shared_ptr<instruction>(new instruction(ADD_ACC{a0}));
      }
      static std::unique_ptr<instruction> NOP__uptr() {
        return std::unique_ptr<instruction>(new instruction(NOP_{}));
      }
      static std::unique_ptr<instruction> INC_PC_uptr() {
        return std::unique_ptr<instruction>(new instruction(INC_PC{}));
      }
      static std::unique_ptr<instruction> ADD_ACC_uptr(unsigned int a0) {
        return std::unique_ptr<instruction>(new instruction(ADD_ACC{a0}));
      }
    };
    const variant_t &v() const { return v_; }
    variant_t &v_mut() { return v_; }
  };

  template <typename T1, MapsTo<T1, unsigned int> F2>
  static T1 instruction_rect(const T1 f, const T1 f0, F2 &&f1,
                             const std::shared_ptr<instruction> &i) {
    return std::visit(
        Overloaded{
            [&](const typename instruction::NOP_ _args) -> T1 { return f; },
            [&](const typename instruction::INC_PC _args) -> T1 { return f0; },
            [&](const typename instruction::ADD_ACC _args) -> T1 {
              unsigned int n = _args._a0;
              return f1(std::move(n));
            }},
        i->v());
  }

  template <typename T1, MapsTo<T1, unsigned int> F2>
  static T1 instruction_rec(const T1 f, const T1 f0, F2 &&f1,
                            const std::shared_ptr<instruction> &i) {
    return std::visit(
        Overloaded{
            [&](const typename instruction::NOP_ _args) -> T1 { return f; },
            [&](const typename instruction::INC_PC _args) -> T1 { return f0; },
            [&](const typename instruction::ADD_ACC _args) -> T1 {
              unsigned int n = _args._a0;
              return f1(std::move(n));
            }},
        i->v());
  }

  static std::shared_ptr<state> execute(std::shared_ptr<state> s,
                                        const std::shared_ptr<instruction> &i);

  static std::shared_ptr<state>
  exec_program(const std::shared_ptr<List<std::shared_ptr<instruction>>> &prog,
               std::shared_ptr<state> s);

  static inline const std::shared_ptr<state> sample =
      std::make_shared<state>(state{0, (0 + 1)});

  static inline const unsigned int t = [](void) {
    std::shared_ptr<state> s_ = exec_program(
        List<std::shared_ptr<instruction>>::ctor::cons_(
            instruction::ctor::INC_PC_(),
            List<std::shared_ptr<instruction>>::ctor::cons_(
                instruction::ctor::ADD_ACC_(((0 + 1) + 1)),
                List<std::shared_ptr<instruction>>::ctor::cons_(
                    instruction::ctor::INC_PC_(),
                    List<std::shared_ptr<instruction>>::ctor::nil_()))),
        sample);
    return (s_->pc_ + s_->acc_);
  }();
};
