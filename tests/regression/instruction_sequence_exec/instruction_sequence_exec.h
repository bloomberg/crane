#ifndef INCLUDED_INSTRUCTION_SEQUENCE_EXEC
#define INCLUDED_INSTRUCTION_SEQUENCE_EXEC

#include <any>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

template <typename A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    A a;
    std::shared_ptr<List<A>> l;
  };

  using variant_t = std::variant<Nil, Cons>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  List() {}

  explicit List(Nil _v) : v_(_v) {}

  explicit List(Cons _v) : v_(std::move(_v)) {}

  template <typename _U> explicit List(const List<_U> &_other) {
    if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
      this->v_ = Nil{};
    } else {
      const auto &[a, l] = std::get<typename List<_U>::Cons>(_other.v());
      this->v_ = Cons{
          [&]() -> A {
            if constexpr (std::is_same_v<_U, std::any>) {
              if (a.type() == typeid(A))
                return std::any_cast<A>(a);
              if constexpr (requires {
                              typename A::first_type;
                              typename A::second_type;
                            }) {
                const auto &[_k, _v] =
                    std::any_cast<std::pair<std::any, std::any>>(a);
                return A{[&]() -> typename A::first_type {
                           if constexpr (std::is_same_v<typename A::first_type,
                                                        std::any>)
                             return _k;
                           else
                             return std::any_cast<typename A::first_type>(_k);
                         }(),
                         [&]() -> typename A::second_type {
                           if constexpr (std::is_same_v<typename A::second_type,
                                                        std::any>)
                             return _v;
                           else
                             return std::any_cast<typename A::second_type>(_v);
                         }()};
              }
              return std::any_cast<A>(a);
            } else
              return A(a);
          }(),
          l ? std::make_shared<List<A>>(*l) : nullptr};
    }
  }

  static List<A> nil() { return List(Nil{}); }

  static List<A> cons(A a, List<A> l) {
    return List(Cons{std::move(a), std::make_shared<List<A>>(std::move(l))});
  }

  // MANIPULATORS
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

struct InstructionSequenceExec {
  struct state {
    uint64_t pc_;
    uint64_t acc_;
  };

  struct instruction {
    // TYPES
    struct NOP_ {};

    struct INC_PC {};

    struct ADD_ACC {
      uint64_t a0;
    };

    using variant_t = std::variant<NOP_, INC_PC, ADD_ACC>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    instruction() {}

    explicit instruction(NOP_ _v) : v_(_v) {}

    explicit instruction(INC_PC _v) : v_(_v) {}

    explicit instruction(ADD_ACC _v) : v_(std::move(_v)) {}

    static instruction nop_() { return instruction(NOP_{}); }

    static instruction inc_pc() { return instruction(INC_PC{}); }

    static instruction add_acc(uint64_t a0) { return instruction(ADD_ACC{a0}); }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename F2>
    requires std::is_invocable_r_v<T1, F2 &, uint64_t &>
  static T1 instruction_rect(T1 f, T1 f0, F2 &&f1, const instruction &i) {
    if (std::holds_alternative<typename instruction::NOP_>(i.v())) {
      return f;
    } else if (std::holds_alternative<typename instruction::INC_PC>(i.v())) {
      return f0;
    } else {
      const auto &[a0] = std::get<typename instruction::ADD_ACC>(i.v());
      return f1(a0);
    }
  }

  template <typename T1, typename F2>
    requires std::is_invocable_r_v<T1, F2 &, uint64_t &>
  static T1 instruction_rec(T1 f, T1 f0, F2 &&f1, const instruction &i) {
    if (std::holds_alternative<typename instruction::NOP_>(i.v())) {
      return f;
    } else if (std::holds_alternative<typename instruction::INC_PC>(i.v())) {
      return f0;
    } else {
      const auto &[a0] = std::get<typename instruction::ADD_ACC>(i.v());
      return f1(a0);
    }
  }

  static state execute(state s, const instruction &i);
  static state exec_program(const List<instruction> &prog, state s);
  static inline const state sample = state{UINT64_C(0), UINT64_C(1)};
  static inline const uint64_t t = []() {
    state s_ = exec_program(
        List<instruction>::cons(
            instruction::inc_pc(),
            List<instruction>::cons(
                instruction::add_acc(UINT64_C(2)),
                List<instruction>::cons(instruction::inc_pc(),
                                        List<instruction>::nil()))),
        sample);
    return (s_.pc_ + s_.acc_);
  }();
};

#endif // INCLUDED_INSTRUCTION_SEQUENCE_EXEC
