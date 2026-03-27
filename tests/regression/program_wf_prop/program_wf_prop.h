#ifndef INCLUDED_PROGRAM_WF_PROP
#define INCLUDED_PROGRAM_WF_PROP

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

  static std::unique_ptr<List<t_A>> nil_uptr() {
    return std::make_unique<List<t_A>>(Nil{});
  }

  static std::unique_ptr<List<t_A>>
  cons_uptr(t_A a0, const std::shared_ptr<List<t_A>> &a1) {
    return std::make_unique<List<t_A>>(Cons{std::move(a0), a1});
  }

  static std::unique_ptr<List<t_A>> cons_uptr(t_A a0,
                                              std::shared_ptr<List<t_A>> &&a1) {
    return std::make_unique<List<t_A>>(Cons{std::move(a0), std::move(a1)});
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

    explicit instruction(NOP _v) : d_v_(std::move(_v)) {}

    static std::shared_ptr<instruction> jun(unsigned int a0) {
      return std::make_shared<instruction>(JUN{std::move(a0)});
    }

    static std::shared_ptr<instruction> jms(unsigned int a0) {
      return std::make_shared<instruction>(JMS{std::move(a0)});
    }

    static std::shared_ptr<instruction> nop() {
      return std::make_shared<instruction>(NOP{});
    }

    static std::unique_ptr<instruction> jun_uptr(unsigned int a0) {
      return std::make_unique<instruction>(JUN{std::move(a0)});
    }

    static std::unique_ptr<instruction> jms_uptr(unsigned int a0) {
      return std::make_unique<instruction>(JMS{std::move(a0)});
    }

    static std::unique_ptr<instruction> nop_uptr() {
      return std::make_unique<instruction>(NOP{});
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
    return std::visit(
        Overloaded{
            [&](const typename instruction::JUN _args) -> T1 {
              return f(_args.d_a0);
            },
            [&](const typename instruction::JMS _args) -> T1 {
              return f0(_args.d_a0);
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
              return f(_args.d_a0);
            },
            [&](const typename instruction::JMS _args) -> T1 {
              return f0(_args.d_a0);
            },
            [&](const typename instruction::NOP _args) -> T1 { return f1; }},
        i->v());
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
