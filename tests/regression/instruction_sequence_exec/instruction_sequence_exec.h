#ifndef INCLUDED_INSTRUCTION_SEQUENCE_EXEC
#define INCLUDED_INSTRUCTION_SEQUENCE_EXEC

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

template <typename t_A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    t_A d_a0;
    std::shared_ptr<List<t_A>> d_a1;
  };

  using variant_t = std::variant<Nil, Cons>;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  explicit List(Nil _v) : d_v_(std::move(_v)) {}

  explicit List(Cons _v) : d_v_(std::move(_v)) {}

  static std::shared_ptr<List<t_A>> nil() {
    return std::make_shared<List<t_A>>(Nil{});
  }

  static std::shared_ptr<List<t_A>> cons(t_A a0,
                                         const std::shared_ptr<List<t_A>> &a1) {
    return std::make_shared<List<t_A>>(Cons{std::move(a0), a1});
  }

  static std::shared_ptr<List<t_A>> cons(t_A a0,
                                         std::shared_ptr<List<t_A>> &&a1) {
    return std::make_shared<List<t_A>>(Cons{std::move(a0), std::move(a1)});
  }

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }
};

struct InstructionSequenceExec {
  struct state {
    unsigned int pc_;
    unsigned int acc_;
  };

  struct instruction {
    // TYPES
    struct NOP_ {};

    struct INC_PC {};

    struct ADD_ACC {
      unsigned int d_a0;
    };

    using variant_t = std::variant<NOP_, INC_PC, ADD_ACC>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    explicit instruction(NOP_ _v) : d_v_(std::move(_v)) {}

    explicit instruction(INC_PC _v) : d_v_(std::move(_v)) {}

    explicit instruction(ADD_ACC _v) : d_v_(std::move(_v)) {}

    static std::shared_ptr<instruction> nop_() {
      return std::make_shared<instruction>(NOP_{});
    }

    static std::shared_ptr<instruction> inc_pc() {
      return std::make_shared<instruction>(INC_PC{});
    }

    static std::shared_ptr<instruction> add_acc(unsigned int a0) {
      return std::make_shared<instruction>(ADD_ACC{std::move(a0)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, MapsTo<T1, unsigned int> F2>
  static T1 instruction_rect(const T1 f, const T1 f0, F2 &&f1,
                             const std::shared_ptr<instruction> &i) {
    return std::visit(
        Overloaded{
            [&](const typename instruction::NOP_ _args) -> T1 { return f; },
            [&](const typename instruction::INC_PC _args) -> T1 { return f0; },
            [&](const typename instruction::ADD_ACC _args) -> T1 {
              return f1(_args.d_a0);
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
              return f1(_args.d_a0);
            }},
        i->v());
  }

  static std::shared_ptr<state> execute(std::shared_ptr<state> s,
                                        const std::shared_ptr<instruction> &i);
  static std::shared_ptr<state>
  exec_program(const std::shared_ptr<List<std::shared_ptr<instruction>>> &prog,
               std::shared_ptr<state> s);
  static inline const std::shared_ptr<state> sample =
      std::make_shared<state>(state{0u, 1u});
  static inline const unsigned int t = []() {
    std::shared_ptr<state> s_ =
        exec_program(List<std::shared_ptr<instruction>>::cons(
                         instruction::inc_pc(),
                         List<std::shared_ptr<instruction>>::cons(
                             instruction::add_acc(2u),
                             List<std::shared_ptr<instruction>>::cons(
                                 instruction::inc_pc(),
                                 List<std::shared_ptr<instruction>>::nil()))),
                     sample);
    return (s_->pc_ + s_->acc_);
  }();
};

#endif // INCLUDED_INSTRUCTION_SEQUENCE_EXEC
