#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <utility>
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

struct Nat {
  static std::pair<unsigned int, unsigned int> divmod(const unsigned int x,
                                                      const unsigned int y,
                                                      const unsigned int q,
                                                      const unsigned int u);

  static unsigned int div(const unsigned int x, const unsigned int y);
};

struct InstructionCycleSum {
  struct state {
    unsigned int acc_;
    bool carry_;
    bool test_;
  };

  static unsigned int acc_(const std::shared_ptr<state> &s);

  static bool carry_(const std::shared_ptr<state> &s);

  static bool test_(const std::shared_ptr<state> &s);

  struct instruction {
  public:
    struct NOP_ {};
    struct JCN_ {
      unsigned int _a0;
    };
    struct INC_ {
      unsigned int _a0;
    };
    using variant_t = std::variant<NOP_, JCN_, INC_>;

  private:
    variant_t v_;
    explicit instruction(NOP_ _v) : v_(std::move(_v)) {}
    explicit instruction(JCN_ _v) : v_(std::move(_v)) {}
    explicit instruction(INC_ _v) : v_(std::move(_v)) {}

  public:
    struct ctor {
      ctor() = delete;
      static std::shared_ptr<instruction> NOP__() {
        return std::shared_ptr<instruction>(new instruction(NOP_{}));
      }
      static std::shared_ptr<instruction> JCN__(unsigned int a0) {
        return std::shared_ptr<instruction>(new instruction(JCN_{a0}));
      }
      static std::shared_ptr<instruction> INC__(unsigned int a0) {
        return std::shared_ptr<instruction>(new instruction(INC_{a0}));
      }
      static std::unique_ptr<instruction> NOP__uptr() {
        return std::unique_ptr<instruction>(new instruction(NOP_{}));
      }
      static std::unique_ptr<instruction> JCN__uptr(unsigned int a0) {
        return std::unique_ptr<instruction>(new instruction(JCN_{a0}));
      }
      static std::unique_ptr<instruction> INC__uptr(unsigned int a0) {
        return std::unique_ptr<instruction>(new instruction(INC_{a0}));
      }
    };
    const variant_t &v() const { return v_; }
    variant_t &v_mut() { return v_; }
  };

  template <typename T1, MapsTo<T1, unsigned int> F1,
            MapsTo<T1, unsigned int> F2>
  static T1 instruction_rect(const T1 f, F1 &&f0, F2 &&f1,
                             const std::shared_ptr<instruction> &i) {
    return std::visit(
        Overloaded{
            [&](const typename instruction::NOP_ _args) -> T1 { return f; },
            [&](const typename instruction::JCN_ _args) -> T1 {
              unsigned int n = _args._a0;
              return f0(std::move(n));
            },
            [&](const typename instruction::INC_ _args) -> T1 {
              unsigned int n = _args._a0;
              return f1(std::move(n));
            }},
        i->v());
  }

  template <typename T1, MapsTo<T1, unsigned int> F1,
            MapsTo<T1, unsigned int> F2>
  static T1 instruction_rec(const T1 f, F1 &&f0, F2 &&f1,
                            const std::shared_ptr<instruction> &i) {
    return std::visit(
        Overloaded{
            [&](const typename instruction::NOP_ _args) -> T1 { return f; },
            [&](const typename instruction::JCN_ _args) -> T1 {
              unsigned int n = _args._a0;
              return f0(std::move(n));
            },
            [&](const typename instruction::INC_ _args) -> T1 {
              unsigned int n = _args._a0;
              return f1(std::move(n));
            }},
        i->v());
  }

  static unsigned int cycles(const std::shared_ptr<state> &s,
                             const std::shared_ptr<instruction> &i);

  static std::shared_ptr<state> execute(std::shared_ptr<state> s,
                                        const std::shared_ptr<instruction> &i);

  static unsigned int program_cycles(
      const std::shared_ptr<state> &s,
      const std::shared_ptr<List<std::shared_ptr<instruction>>> &prog);

  static inline const unsigned int t = program_cycles(
      std::make_shared<state>(state{0, false, true}),
      List<std::shared_ptr<instruction>>::ctor::cons_(
          instruction::ctor::JCN__(
              ((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1)),
          List<std::shared_ptr<instruction>>::ctor::cons_(
              instruction::ctor::INC__(0),
              List<std::shared_ptr<instruction>>::ctor::cons_(
                  instruction::ctor::NOP__(),
                  List<std::shared_ptr<instruction>>::ctor::nil_()))));
};
