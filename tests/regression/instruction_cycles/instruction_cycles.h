#ifndef INCLUDED_INSTRUCTION_CYCLES
#define INCLUDED_INSTRUCTION_CYCLES

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

  // CREATORS
  explicit List(Nil _v) : d_v_(std::move(_v)) {}

  explicit List(Cons _v) : d_v_(std::move(_v)) {}

public:
  // TYPES
  struct ctor {
    ctor() = delete;

    static std::shared_ptr<List<t_A>> Nil_() {
      return std::shared_ptr<List<t_A>>(new List<t_A>(Nil{}));
    }

    static std::shared_ptr<List<t_A>>
    Cons_(t_A a0, const std::shared_ptr<List<t_A>> &a1) {
      return std::shared_ptr<List<t_A>>(new List<t_A>(Cons{a0, a1}));
    }

    static std::unique_ptr<List<t_A>> Nil_uptr() {
      return std::unique_ptr<List<t_A>>(new List<t_A>(Nil{}));
    }

    static std::unique_ptr<List<t_A>>
    Cons_uptr(t_A a0, const std::shared_ptr<List<t_A>> &a1) {
      return std::unique_ptr<List<t_A>>(new List<t_A>(Cons{a0, a1}));
    }
  };

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }

  template <MapsTo<bool, t_A> F0>
  __attribute__((pure)) bool forallb(F0 &&f) const {
    return std::visit(
        Overloaded{
            [](const typename List<t_A>::Nil _args) -> bool { return true; },
            [&](const typename List<t_A>::Cons _args) -> bool {
              t_A a = _args.d_a0;
              std::shared_ptr<List<t_A>> l0 = _args.d_a1;
              return (f(a) && std::move(l0)->forallb(f));
            }},
        this->v());
  }
};

struct Nat {
  __attribute__((pure)) static std::pair<unsigned int, unsigned int>
  divmod(const unsigned int x, const unsigned int y, const unsigned int q,
         const unsigned int u);
  __attribute__((pure)) static unsigned int div(const unsigned int x,
                                                const unsigned int y);
};

struct InstructionCycles {
  struct state1 {
    unsigned int acc1;
    bool carry1;
    bool test_pin1;
  };

  struct instruction1 {
    // TYPES
    struct JCN1 {
      unsigned int d_a0;
      unsigned int d_a1;
    };

    struct NOP1 {};

    using variant_t = std::variant<JCN1, NOP1>;

  private:
    // DATA
    variant_t d_v_;

    // CREATORS
    explicit instruction1(JCN1 _v) : d_v_(std::move(_v)) {}

    explicit instruction1(NOP1 _v) : d_v_(std::move(_v)) {}

  public:
    // TYPES
    struct ctor {
      ctor() = delete;

      static std::shared_ptr<instruction1> JCN1_(unsigned int a0,
                                                 unsigned int a1) {
        return std::shared_ptr<instruction1>(new instruction1(JCN1{a0, a1}));
      }

      static std::shared_ptr<instruction1> NOP1_() {
        return std::shared_ptr<instruction1>(new instruction1(NOP1{}));
      }

      static std::unique_ptr<instruction1> JCN1_uptr(unsigned int a0,
                                                     unsigned int a1) {
        return std::unique_ptr<instruction1>(new instruction1(JCN1{a0, a1}));
      }

      static std::unique_ptr<instruction1> NOP1_uptr() {
        return std::unique_ptr<instruction1>(new instruction1(NOP1{}));
      }
    };

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, MapsTo<T1, unsigned int, unsigned int> F0>
  static T1 instruction1_rect(F0 &&f, const T1 f0,
                              const std::shared_ptr<instruction1> &i) {
    return std::visit(
        Overloaded{
            [&](const typename instruction1::JCN1 _args) -> T1 {
              unsigned int n = _args.d_a0;
              unsigned int n0 = _args.d_a1;
              return f(std::move(n), std::move(n0));
            },
            [&](const typename instruction1::NOP1 _args) -> T1 { return f0; }},
        i->v());
  }

  template <typename T1, MapsTo<T1, unsigned int, unsigned int> F0>
  static T1 instruction1_rec(F0 &&f, const T1 f0,
                             const std::shared_ptr<instruction1> &i) {
    return std::visit(
        Overloaded{
            [&](const typename instruction1::JCN1 _args) -> T1 {
              unsigned int n = _args.d_a0;
              unsigned int n0 = _args.d_a1;
              return f(std::move(n), std::move(n0));
            },
            [&](const typename instruction1::NOP1 _args) -> T1 { return f0; }},
        i->v());
  }

  __attribute__((pure)) static unsigned int
  cycles_jcn(const std::shared_ptr<state1> &s,
             const std::shared_ptr<instruction1> &i);
  static inline const unsigned int test_cycles_jcn_not_taken =
      cycles_jcn(std::make_shared<state1>(state1{1u, false, true}),
                 instruction1::ctor::JCN1_(4u, 7u));

  struct instruction2 {
    // TYPES
    struct JMS2 {
      unsigned int d_a0;
    };

    struct NOP2 {};

    using variant_t = std::variant<JMS2, NOP2>;

  private:
    // DATA
    variant_t d_v_;

    // CREATORS
    explicit instruction2(JMS2 _v) : d_v_(std::move(_v)) {}

    explicit instruction2(NOP2 _v) : d_v_(std::move(_v)) {}

  public:
    // TYPES
    struct ctor {
      ctor() = delete;

      static std::shared_ptr<instruction2> JMS2_(unsigned int a0) {
        return std::shared_ptr<instruction2>(new instruction2(JMS2{a0}));
      }

      static std::shared_ptr<instruction2> NOP2_() {
        return std::shared_ptr<instruction2>(new instruction2(NOP2{}));
      }

      static std::unique_ptr<instruction2> JMS2_uptr(unsigned int a0) {
        return std::unique_ptr<instruction2>(new instruction2(JMS2{a0}));
      }

      static std::unique_ptr<instruction2> NOP2_uptr() {
        return std::unique_ptr<instruction2>(new instruction2(NOP2{}));
      }
    };

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, MapsTo<T1, unsigned int> F0>
  static T1 instruction2_rect(F0 &&f, const T1 f0,
                              const std::shared_ptr<instruction2> &i) {
    return std::visit(
        Overloaded{
            [&](const typename instruction2::JMS2 _args) -> T1 {
              unsigned int n = _args.d_a0;
              return f(std::move(n));
            },
            [&](const typename instruction2::NOP2 _args) -> T1 { return f0; }},
        i->v());
  }

  template <typename T1, MapsTo<T1, unsigned int> F0>
  static T1 instruction2_rec(F0 &&f, const T1 f0,
                             const std::shared_ptr<instruction2> &i) {
    return std::visit(
        Overloaded{
            [&](const typename instruction2::JMS2 _args) -> T1 {
              unsigned int n = _args.d_a0;
              return f(std::move(n));
            },
            [&](const typename instruction2::NOP2 _args) -> T1 { return f0; }},
        i->v());
  }

  struct state2 {
    unsigned int acc2;
  };

  __attribute__((pure)) static unsigned int
  cycles_jms(const std::shared_ptr<state2> &_x,
             const std::shared_ptr<instruction2> &i);
  static inline const unsigned int test_cycles_jms_constant = cycles_jms(
      std::make_shared<state2>(state2{0u}), instruction2::ctor::JMS2_(77u));
  enum class Instr3 {
    e_NOP3,
    e_ADD3,
    e_WRM3,
    e_FIM3,
    e_JMS3,
    e_JCNTAKEN3,
    e_JCNNOTTAKEN3,
    e_ISZTAKEN3,
    e_ISZZERO3
  };

  template <typename T1>
  static T1 instr3_rect(const T1 f, const T1 f0, const T1 f1, const T1 f2,
                        const T1 f3, const T1 f4, const T1 f5, const T1 f6,
                        const T1 f7, const Instr3 i) {
    return [&](void) {
      switch (i) {
      case Instr3::e_NOP3: {
        return f;
      }
      case Instr3::e_ADD3: {
        return f0;
      }
      case Instr3::e_WRM3: {
        return f1;
      }
      case Instr3::e_FIM3: {
        return f2;
      }
      case Instr3::e_JMS3: {
        return f3;
      }
      case Instr3::e_JCNTAKEN3: {
        return f4;
      }
      case Instr3::e_JCNNOTTAKEN3: {
        return f5;
      }
      case Instr3::e_ISZTAKEN3: {
        return f6;
      }
      case Instr3::e_ISZZERO3: {
        return f7;
      }
      }
    }();
  }

  template <typename T1>
  static T1 instr3_rec(const T1 f, const T1 f0, const T1 f1, const T1 f2,
                       const T1 f3, const T1 f4, const T1 f5, const T1 f6,
                       const T1 f7, const Instr3 i) {
    return [&](void) {
      switch (i) {
      case Instr3::e_NOP3: {
        return f;
      }
      case Instr3::e_ADD3: {
        return f0;
      }
      case Instr3::e_WRM3: {
        return f1;
      }
      case Instr3::e_FIM3: {
        return f2;
      }
      case Instr3::e_JMS3: {
        return f3;
      }
      case Instr3::e_JCNTAKEN3: {
        return f4;
      }
      case Instr3::e_JCNNOTTAKEN3: {
        return f5;
      }
      case Instr3::e_ISZTAKEN3: {
        return f6;
      }
      case Instr3::e_ISZZERO3: {
        return f7;
      }
      }
    }();
  }

  __attribute__((pure)) static unsigned int cycles_min(const Instr3 i);
  static inline const std::shared_ptr<List<Instr3>> all_instrs3 =
      List<Instr3>::ctor::Cons_(
          Instr3::e_NOP3,
          List<Instr3>::ctor::Cons_(
              Instr3::e_ADD3,
              List<Instr3>::ctor::Cons_(
                  Instr3::e_WRM3,
                  List<Instr3>::ctor::Cons_(
                      Instr3::e_FIM3,
                      List<Instr3>::ctor::Cons_(
                          Instr3::e_JMS3,
                          List<Instr3>::ctor::Cons_(
                              Instr3::e_JCNTAKEN3,
                              List<Instr3>::ctor::Cons_(
                                  Instr3::e_JCNNOTTAKEN3,
                                  List<Instr3>::ctor::Cons_(
                                      Instr3::e_ISZTAKEN3,
                                      List<Instr3>::ctor::Cons_(
                                          Instr3::e_ISZZERO3,
                                          List<Instr3>::ctor::Nil_())))))))));
  static inline const bool test_min_cycles_per_instruction =
      all_instrs3->forallb([](Instr3 i) { return 8u <= cycles_min(i); });
  enum class Instr4 {
    e_NOP4,
    e_ADD4,
    e_WRM4,
    e_FIM4,
    e_JMS4,
    e_JCNTAKEN4,
    e_JCNNOTTAKEN4,
    e_ISZTAKEN4,
    e_ISZZERO4
  };

  template <typename T1>
  static T1 instr4_rect(const T1 f, const T1 f0, const T1 f1, const T1 f2,
                        const T1 f3, const T1 f4, const T1 f5, const T1 f6,
                        const T1 f7, const Instr4 i) {
    return [&](void) {
      switch (i) {
      case Instr4::e_NOP4: {
        return f;
      }
      case Instr4::e_ADD4: {
        return f0;
      }
      case Instr4::e_WRM4: {
        return f1;
      }
      case Instr4::e_FIM4: {
        return f2;
      }
      case Instr4::e_JMS4: {
        return f3;
      }
      case Instr4::e_JCNTAKEN4: {
        return f4;
      }
      case Instr4::e_JCNNOTTAKEN4: {
        return f5;
      }
      case Instr4::e_ISZTAKEN4: {
        return f6;
      }
      case Instr4::e_ISZZERO4: {
        return f7;
      }
      }
    }();
  }

  template <typename T1>
  static T1 instr4_rec(const T1 f, const T1 f0, const T1 f1, const T1 f2,
                       const T1 f3, const T1 f4, const T1 f5, const T1 f6,
                       const T1 f7, const Instr4 i) {
    return [&](void) {
      switch (i) {
      case Instr4::e_NOP4: {
        return f;
      }
      case Instr4::e_ADD4: {
        return f0;
      }
      case Instr4::e_WRM4: {
        return f1;
      }
      case Instr4::e_FIM4: {
        return f2;
      }
      case Instr4::e_JMS4: {
        return f3;
      }
      case Instr4::e_JCNTAKEN4: {
        return f4;
      }
      case Instr4::e_JCNNOTTAKEN4: {
        return f5;
      }
      case Instr4::e_ISZTAKEN4: {
        return f6;
      }
      case Instr4::e_ISZZERO4: {
        return f7;
      }
      }
    }();
  }

  __attribute__((pure)) static unsigned int cycles_max(const Instr4 i);
  static inline const std::shared_ptr<List<Instr4>> all_instrs4 =
      List<Instr4>::ctor::Cons_(
          Instr4::e_NOP4,
          List<Instr4>::ctor::Cons_(
              Instr4::e_ADD4,
              List<Instr4>::ctor::Cons_(
                  Instr4::e_WRM4,
                  List<Instr4>::ctor::Cons_(
                      Instr4::e_FIM4,
                      List<Instr4>::ctor::Cons_(
                          Instr4::e_JMS4,
                          List<Instr4>::ctor::Cons_(
                              Instr4::e_JCNTAKEN4,
                              List<Instr4>::ctor::Cons_(
                                  Instr4::e_JCNNOTTAKEN4,
                                  List<Instr4>::ctor::Cons_(
                                      Instr4::e_ISZTAKEN4,
                                      List<Instr4>::ctor::Cons_(
                                          Instr4::e_ISZZERO4,
                                          List<Instr4>::ctor::Nil_())))))))));
  static inline const bool test_max_cycles_per_instruction =
      all_instrs4->forallb([](Instr4 i) { return cycles_max(i) <= 24u; });

  struct state5 {
    unsigned int acc5;
    bool carry5;
    bool test5;
  };

  struct instruction5 {
    // TYPES
    struct NOP5 {};

    struct JCN5 {
      unsigned int d_a0;
    };

    struct INC5 {
      unsigned int d_a0;
    };

    using variant_t = std::variant<NOP5, JCN5, INC5>;

  private:
    // DATA
    variant_t d_v_;

    // CREATORS
    explicit instruction5(NOP5 _v) : d_v_(std::move(_v)) {}

    explicit instruction5(JCN5 _v) : d_v_(std::move(_v)) {}

    explicit instruction5(INC5 _v) : d_v_(std::move(_v)) {}

  public:
    // TYPES
    struct ctor {
      ctor() = delete;

      static std::shared_ptr<instruction5> NOP5_() {
        return std::shared_ptr<instruction5>(new instruction5(NOP5{}));
      }

      static std::shared_ptr<instruction5> JCN5_(unsigned int a0) {
        return std::shared_ptr<instruction5>(new instruction5(JCN5{a0}));
      }

      static std::shared_ptr<instruction5> INC5_(unsigned int a0) {
        return std::shared_ptr<instruction5>(new instruction5(INC5{a0}));
      }

      static std::unique_ptr<instruction5> NOP5_uptr() {
        return std::unique_ptr<instruction5>(new instruction5(NOP5{}));
      }

      static std::unique_ptr<instruction5> JCN5_uptr(unsigned int a0) {
        return std::unique_ptr<instruction5>(new instruction5(JCN5{a0}));
      }

      static std::unique_ptr<instruction5> INC5_uptr(unsigned int a0) {
        return std::unique_ptr<instruction5>(new instruction5(INC5{a0}));
      }
    };

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, MapsTo<T1, unsigned int> F1,
            MapsTo<T1, unsigned int> F2>
  static T1 instruction5_rect(const T1 f, F1 &&f0, F2 &&f1,
                              const std::shared_ptr<instruction5> &i) {
    return std::visit(
        Overloaded{
            [&](const typename instruction5::NOP5 _args) -> T1 { return f; },
            [&](const typename instruction5::JCN5 _args) -> T1 {
              unsigned int n = _args.d_a0;
              return f0(std::move(n));
            },
            [&](const typename instruction5::INC5 _args) -> T1 {
              unsigned int n = _args.d_a0;
              return f1(std::move(n));
            }},
        i->v());
  }

  template <typename T1, MapsTo<T1, unsigned int> F1,
            MapsTo<T1, unsigned int> F2>
  static T1 instruction5_rec(const T1 f, F1 &&f0, F2 &&f1,
                             const std::shared_ptr<instruction5> &i) {
    return std::visit(
        Overloaded{
            [&](const typename instruction5::NOP5 _args) -> T1 { return f; },
            [&](const typename instruction5::JCN5 _args) -> T1 {
              unsigned int n = _args.d_a0;
              return f0(std::move(n));
            },
            [&](const typename instruction5::INC5 _args) -> T1 {
              unsigned int n = _args.d_a0;
              return f1(std::move(n));
            }},
        i->v());
  }

  __attribute__((pure)) static unsigned int
  cycles_sum(const std::shared_ptr<state5> &s,
             const std::shared_ptr<instruction5> &i);
  static std::shared_ptr<state5>
  execute5(std::shared_ptr<state5> s, const std::shared_ptr<instruction5> &i);
  __attribute__((pure)) static unsigned int program_cycles5(
      const std::shared_ptr<state5> &s,
      const std::shared_ptr<List<std::shared_ptr<instruction5>>> &prog);
  static inline const unsigned int test_instruction_cycle_sum = program_cycles5(
      std::make_shared<state5>(state5{0u, false, true}),
      List<std::shared_ptr<instruction5>>::ctor::Cons_(
          instruction5::ctor::JCN5_(8u),
          List<std::shared_ptr<instruction5>>::ctor::Cons_(
              instruction5::ctor::INC5_(0u),
              List<std::shared_ptr<instruction5>>::ctor::Cons_(
                  instruction5::ctor::NOP5_(),
                  List<std::shared_ptr<instruction5>>::ctor::Nil_()))));
  enum class Instruction6 { e_NOP6 };

  template <typename T1>
  static T1 instruction6_rect(const T1 f, const Instruction6 i) {
    return [&](void) {
      switch (i) {
      case Instruction6::e_NOP6: {
        return f;
      }
      }
    }();
  }

  template <typename T1>
  static T1 instruction6_rec(const T1 f, const Instruction6 i) {
    return [&](void) {
      switch (i) {
      case Instruction6::e_NOP6: {
        return f;
      }
      }
    }();
  }

  struct state6 {
    unsigned int acc6;
  };

  __attribute__((pure)) static unsigned int
  cycles6(const std::shared_ptr<state6> &_x, const Instruction6 _x0);
  __attribute__((pure)) static unsigned int
  program_cycles6(const std::shared_ptr<state6> &s,
                  const std::shared_ptr<List<Instruction6>> &prog);
  static inline const unsigned int singleton_cycles6 = program_cycles6(
      std::make_shared<state6>(state6{0u}),
      List<Instruction6>::ctor::Cons_(Instruction6::e_NOP6,
                                      List<Instruction6>::ctor::Nil_()));
  static inline const unsigned int three_nop_cycles6 = program_cycles6(
      std::make_shared<state6>(state6{0u}),
      List<Instruction6>::ctor::Cons_(
          Instruction6::e_NOP6,
          List<Instruction6>::ctor::Cons_(
              Instruction6::e_NOP6,
              List<Instruction6>::ctor::Cons_(
                  Instruction6::e_NOP6, List<Instruction6>::ctor::Nil_()))));
  static inline const std::pair<unsigned int, unsigned int>
      test_program_cycles =
          std::make_pair(singleton_cycles6, three_nop_cycles6);
  enum class Instruction7 { e_NOP7 };

  template <typename T1>
  static T1 instruction7_rect(const T1 f, const Instruction7 i) {
    return [&](void) {
      switch (i) {
      case Instruction7::e_NOP7: {
        return f;
      }
      }
    }();
  }

  template <typename T1>
  static T1 instruction7_rec(const T1 f, const Instruction7 i) {
    return [&](void) {
      switch (i) {
      case Instruction7::e_NOP7: {
        return f;
      }
      }
    }();
  }

  struct state7 {
    unsigned int acc7;
  };

  __attribute__((pure)) static unsigned int
  cycles7(const std::shared_ptr<state7> &_x, const Instruction7 _x0);
  __attribute__((pure)) static unsigned int
  program_cycles7(const std::shared_ptr<state7> &s,
                  const std::shared_ptr<List<Instruction7>> &prog);
  static inline const unsigned int test_program_cycles_single = program_cycles7(
      std::make_shared<state7>(state7{16u}),
      List<Instruction7>::ctor::Cons_(Instruction7::e_NOP7,
                                      List<Instruction7>::ctor::Nil_()));
  static inline const std::pair<
      std::pair<
          std::pair<
              std::pair<std::pair<std::pair<unsigned int, unsigned int>, bool>,
                        bool>,
              unsigned int>,
          std::pair<unsigned int, unsigned int>>,
      unsigned int>
      t = std::make_pair(
          std::make_pair(
              std::make_pair(
                  std::make_pair(
                      std::make_pair(std::make_pair(test_cycles_jcn_not_taken,
                                                    test_cycles_jms_constant),
                                     test_min_cycles_per_instruction),
                      test_max_cycles_per_instruction),
                  test_instruction_cycle_sum),
              test_program_cycles),
          test_program_cycles_single);
};

#endif // INCLUDED_INSTRUCTION_CYCLES
