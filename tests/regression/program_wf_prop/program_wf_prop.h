#ifndef INCLUDED_PROGRAM_WF_PROP
#define INCLUDED_PROGRAM_WF_PROP

#include <memory>
#include <optional>
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
  explicit List(Nil _v) : d_v_(_v) {}

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

struct ProgramWfProp {
  struct instruction {
    // TYPES
    struct JUN {
      unsigned int d_a0;
    };

    struct JMS {
      unsigned int d_a0;
    };

    struct NOP {};

    using variant_t = std::variant<JUN, JMS, NOP>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    explicit instruction(JUN _v) : d_v_(std::move(_v)) {}

    explicit instruction(JMS _v) : d_v_(std::move(_v)) {}

    explicit instruction(NOP _v) : d_v_(_v) {}

    static std::shared_ptr<instruction> jun(unsigned int a0) {
      return std::make_shared<instruction>(JUN{std::move(a0)});
    }

    static std::shared_ptr<instruction> jms(unsigned int a0) {
      return std::make_shared<instruction>(JMS{std::move(a0)});
    }

    static std::shared_ptr<instruction> nop() {
      return std::make_shared<instruction>(NOP{});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, MapsTo<T1, unsigned int> F0,
            MapsTo<T1, unsigned int> F1>
  static T1 instruction_rect(F0 &&f, F1 &&f0, const T1 f1,
                             const std::shared_ptr<instruction> &i) {
    if (std::holds_alternative<typename instruction::JUN>(i->v())) {
      const auto &[d_a0] = std::get<typename instruction::JUN>(i->v());
      return f(d_a0);
    } else if (std::holds_alternative<typename instruction::JMS>(i->v())) {
      const auto &[d_a0] = std::get<typename instruction::JMS>(i->v());
      return f0(d_a0);
    } else {
      return f1;
    }
  }

  template <typename T1, MapsTo<T1, unsigned int> F0,
            MapsTo<T1, unsigned int> F1>
  static T1 instruction_rec(F0 &&f, F1 &&f0, const T1 f1,
                            const std::shared_ptr<instruction> &i) {
    if (std::holds_alternative<typename instruction::JUN>(i->v())) {
      const auto &[d_a0] = std::get<typename instruction::JUN>(i->v());
      return f(d_a0);
    } else if (std::holds_alternative<typename instruction::JMS>(i->v())) {
      const auto &[d_a0] = std::get<typename instruction::JMS>(i->v());
      return f0(d_a0);
    } else {
      return f1;
    }
  }

  struct layout {
    unsigned int base_addr;
    unsigned int code_size;
  };

  __attribute__((pure)) static std::optional<unsigned int>
  jump_target(const std::shared_ptr<instruction> &i);
  static inline const std::shared_ptr<layout> sample_layout =
      std::make_shared<layout>(layout{200u, 20u});
  static inline const std::shared_ptr<List<std::shared_ptr<instruction>>>
      sample_prog = List<std::shared_ptr<instruction>>::cons(
          instruction::nop(),
          List<std::shared_ptr<instruction>>::cons(
              instruction::jun(205u),
              List<std::shared_ptr<instruction>>::cons(
                  instruction::jms(218u),
                  List<std::shared_ptr<instruction>>::nil())));
};

#endif // INCLUDED_PROGRAM_WF_PROP
