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
  // TYPES
  struct nil {};

  struct cons {
    A _a0;
    std::shared_ptr<List<A>> _a1;
  };

  using variant_t = std::variant<nil, cons>;

private:
  // DATA
  variant_t v_;

  // CREATORS
  explicit List(nil _v) : v_(std::move(_v)) {}

  explicit List(cons _v) : v_(std::move(_v)) {}

public:
  // TYPES
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

  // MANIPULATORS
  variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  template <MapsTo<bool, A> F0> bool forallb(F0 &&f) const {
    return std::visit(
        Overloaded{
            [](const typename List<A>::nil _args) -> bool { return true; },
            [&](const typename List<A>::cons _args) -> bool {
              A a = _args._a0;
              std::shared_ptr<List<A>> l0 = _args._a1;
              return (f(a) && std::move(l0)->forallb(f));
            }},
        this->v());
  }
};

struct Nat {
  static std::pair<unsigned int, unsigned int> divmod(const unsigned int x,
                                                      const unsigned int y,
                                                      const unsigned int q,
                                                      const unsigned int u);
  static unsigned int div(const unsigned int x, const unsigned int y);
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
      unsigned int _a0;
      unsigned int _a1;
    };

    struct NOP1 {};

    using variant_t = std::variant<JCN1, NOP1>;

  private:
    // DATA
    variant_t v_;

    // CREATORS
    explicit instruction1(JCN1 _v) : v_(std::move(_v)) {}

    explicit instruction1(NOP1 _v) : v_(std::move(_v)) {}

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
    variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, MapsTo<T1, unsigned int, unsigned int> F0>
  static T1 instruction1_rect(F0 &&f, const T1 f0,
                              const std::shared_ptr<instruction1> &i) {
    return std::visit(
        Overloaded{
            [&](const typename instruction1::JCN1 _args) -> T1 {
              unsigned int n = _args._a0;
              unsigned int n0 = _args._a1;
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
              unsigned int n = _args._a0;
              unsigned int n0 = _args._a1;
              return f(std::move(n), std::move(n0));
            },
            [&](const typename instruction1::NOP1 _args) -> T1 { return f0; }},
        i->v());
  }

  static unsigned int cycles_jcn(const std::shared_ptr<state1> &s,
                                 const std::shared_ptr<instruction1> &i);
  static inline const unsigned int test_cycles_jcn_not_taken =
      cycles_jcn(std::make_shared<state1>(state1{1u, false, true}),
                 instruction1::ctor::JCN1_(4u, 7u));

  struct instruction2 {
    // TYPES
    struct JMS2 {
      unsigned int _a0;
    };

    struct NOP2 {};

    using variant_t = std::variant<JMS2, NOP2>;

  private:
    // DATA
    variant_t v_;

    // CREATORS
    explicit instruction2(JMS2 _v) : v_(std::move(_v)) {}

    explicit instruction2(NOP2 _v) : v_(std::move(_v)) {}

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
    variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, MapsTo<T1, unsigned int> F0>
  static T1 instruction2_rect(F0 &&f, const T1 f0,
                              const std::shared_ptr<instruction2> &i) {
    return std::visit(
        Overloaded{
            [&](const typename instruction2::JMS2 _args) -> T1 {
              unsigned int n = _args._a0;
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
              unsigned int n = _args._a0;
              return f(std::move(n));
            },
            [&](const typename instruction2::NOP2 _args) -> T1 { return f0; }},
        i->v());
  }

  struct state2 {
    unsigned int acc2;
  };

  static unsigned int cycles_jms(const std::shared_ptr<state2> &_x,
                                 const std::shared_ptr<instruction2> &i);
  static inline const unsigned int test_cycles_jms_constant = cycles_jms(
      std::make_shared<state2>(state2{0u}), instruction2::ctor::JMS2_(77u));
  enum class instr3 {
    NOP3,
    ADD3,
    WRM3,
    FIM3,
    JMS3,
    JCNTaken3,
    JCNNotTaken3,
    ISZTaken3,
    ISZZero3
  };

  template <typename T1>
  static T1 instr3_rect(const T1 f, const T1 f0, const T1 f1, const T1 f2,
                        const T1 f3, const T1 f4, const T1 f5, const T1 f6,
                        const T1 f7, const instr3 i) {
    return [&](void) {
      switch (i) {
      case instr3::NOP3: {
        return f;
      }
      case instr3::ADD3: {
        return f0;
      }
      case instr3::WRM3: {
        return f1;
      }
      case instr3::FIM3: {
        return f2;
      }
      case instr3::JMS3: {
        return f3;
      }
      case instr3::JCNTaken3: {
        return f4;
      }
      case instr3::JCNNotTaken3: {
        return f5;
      }
      case instr3::ISZTaken3: {
        return f6;
      }
      case instr3::ISZZero3: {
        return f7;
      }
      }
    }();
  }

  template <typename T1>
  static T1 instr3_rec(const T1 f, const T1 f0, const T1 f1, const T1 f2,
                       const T1 f3, const T1 f4, const T1 f5, const T1 f6,
                       const T1 f7, const instr3 i) {
    return [&](void) {
      switch (i) {
      case instr3::NOP3: {
        return f;
      }
      case instr3::ADD3: {
        return f0;
      }
      case instr3::WRM3: {
        return f1;
      }
      case instr3::FIM3: {
        return f2;
      }
      case instr3::JMS3: {
        return f3;
      }
      case instr3::JCNTaken3: {
        return f4;
      }
      case instr3::JCNNotTaken3: {
        return f5;
      }
      case instr3::ISZTaken3: {
        return f6;
      }
      case instr3::ISZZero3: {
        return f7;
      }
      }
    }();
  }

  static unsigned int cycles_min(const instr3 i);
  static inline const std::shared_ptr<List<instr3>> all_instrs3 =
      List<instr3>::ctor::cons_(
          instr3::NOP3,
          List<instr3>::ctor::cons_(
              instr3::ADD3,
              List<instr3>::ctor::cons_(
                  instr3::WRM3,
                  List<instr3>::ctor::cons_(
                      instr3::FIM3,
                      List<instr3>::ctor::cons_(
                          instr3::JMS3,
                          List<instr3>::ctor::cons_(
                              instr3::JCNTaken3,
                              List<instr3>::ctor::cons_(
                                  instr3::JCNNotTaken3,
                                  List<instr3>::ctor::cons_(
                                      instr3::ISZTaken3,
                                      List<instr3>::ctor::cons_(
                                          instr3::ISZZero3,
                                          List<instr3>::ctor::nil_())))))))));
  static inline const bool test_min_cycles_per_instruction =
      all_instrs3->forallb([](instr3 i) { return (8u <= cycles_min(i)); });
  enum class instr4 {
    NOP4,
    ADD4,
    WRM4,
    FIM4,
    JMS4,
    JCNTaken4,
    JCNNotTaken4,
    ISZTaken4,
    ISZZero4
  };

  template <typename T1>
  static T1 instr4_rect(const T1 f, const T1 f0, const T1 f1, const T1 f2,
                        const T1 f3, const T1 f4, const T1 f5, const T1 f6,
                        const T1 f7, const instr4 i) {
    return [&](void) {
      switch (i) {
      case instr4::NOP4: {
        return f;
      }
      case instr4::ADD4: {
        return f0;
      }
      case instr4::WRM4: {
        return f1;
      }
      case instr4::FIM4: {
        return f2;
      }
      case instr4::JMS4: {
        return f3;
      }
      case instr4::JCNTaken4: {
        return f4;
      }
      case instr4::JCNNotTaken4: {
        return f5;
      }
      case instr4::ISZTaken4: {
        return f6;
      }
      case instr4::ISZZero4: {
        return f7;
      }
      }
    }();
  }

  template <typename T1>
  static T1 instr4_rec(const T1 f, const T1 f0, const T1 f1, const T1 f2,
                       const T1 f3, const T1 f4, const T1 f5, const T1 f6,
                       const T1 f7, const instr4 i) {
    return [&](void) {
      switch (i) {
      case instr4::NOP4: {
        return f;
      }
      case instr4::ADD4: {
        return f0;
      }
      case instr4::WRM4: {
        return f1;
      }
      case instr4::FIM4: {
        return f2;
      }
      case instr4::JMS4: {
        return f3;
      }
      case instr4::JCNTaken4: {
        return f4;
      }
      case instr4::JCNNotTaken4: {
        return f5;
      }
      case instr4::ISZTaken4: {
        return f6;
      }
      case instr4::ISZZero4: {
        return f7;
      }
      }
    }();
  }

  static unsigned int cycles_max(const instr4 i);
  static inline const std::shared_ptr<List<instr4>> all_instrs4 =
      List<instr4>::ctor::cons_(
          instr4::NOP4,
          List<instr4>::ctor::cons_(
              instr4::ADD4,
              List<instr4>::ctor::cons_(
                  instr4::WRM4,
                  List<instr4>::ctor::cons_(
                      instr4::FIM4,
                      List<instr4>::ctor::cons_(
                          instr4::JMS4,
                          List<instr4>::ctor::cons_(
                              instr4::JCNTaken4,
                              List<instr4>::ctor::cons_(
                                  instr4::JCNNotTaken4,
                                  List<instr4>::ctor::cons_(
                                      instr4::ISZTaken4,
                                      List<instr4>::ctor::cons_(
                                          instr4::ISZZero4,
                                          List<instr4>::ctor::nil_())))))))));
  static inline const bool test_max_cycles_per_instruction =
      all_instrs4->forallb([](instr4 i) { return (cycles_max(i) <= 24u); });

  struct state5 {
    unsigned int acc5;
    bool carry5;
    bool test5;
  };

  struct instruction5 {
    // TYPES
    struct NOP5 {};

    struct JCN5 {
      unsigned int _a0;
    };

    struct INC5 {
      unsigned int _a0;
    };

    using variant_t = std::variant<NOP5, JCN5, INC5>;

  private:
    // DATA
    variant_t v_;

    // CREATORS
    explicit instruction5(NOP5 _v) : v_(std::move(_v)) {}

    explicit instruction5(JCN5 _v) : v_(std::move(_v)) {}

    explicit instruction5(INC5 _v) : v_(std::move(_v)) {}

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
    variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, MapsTo<T1, unsigned int> F1,
            MapsTo<T1, unsigned int> F2>
  static T1 instruction5_rect(const T1 f, F1 &&f0, F2 &&f1,
                              const std::shared_ptr<instruction5> &i) {
    return std::visit(
        Overloaded{
            [&](const typename instruction5::NOP5 _args) -> T1 { return f; },
            [&](const typename instruction5::JCN5 _args) -> T1 {
              unsigned int n = _args._a0;
              return f0(std::move(n));
            },
            [&](const typename instruction5::INC5 _args) -> T1 {
              unsigned int n = _args._a0;
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
              unsigned int n = _args._a0;
              return f0(std::move(n));
            },
            [&](const typename instruction5::INC5 _args) -> T1 {
              unsigned int n = _args._a0;
              return f1(std::move(n));
            }},
        i->v());
  }

  static unsigned int cycles_sum(const std::shared_ptr<state5> &s,
                                 const std::shared_ptr<instruction5> &i);
  static std::shared_ptr<state5>
  execute5(std::shared_ptr<state5> s, const std::shared_ptr<instruction5> &i);
  static unsigned int program_cycles5(
      const std::shared_ptr<state5> &s,
      const std::shared_ptr<List<std::shared_ptr<instruction5>>> &prog);
  static inline const unsigned int test_instruction_cycle_sum = program_cycles5(
      std::make_shared<state5>(state5{0u, false, true}),
      List<std::shared_ptr<instruction5>>::ctor::cons_(
          instruction5::ctor::JCN5_(8u),
          List<std::shared_ptr<instruction5>>::ctor::cons_(
              instruction5::ctor::INC5_(0u),
              List<std::shared_ptr<instruction5>>::ctor::cons_(
                  instruction5::ctor::NOP5_(),
                  List<std::shared_ptr<instruction5>>::ctor::nil_()))));
  enum class instruction6 { NOP6 };

  template <typename T1>
  static T1 instruction6_rect(const T1 f, const instruction6 i) {
    return [&](void) {
      switch (i) {
      case instruction6::NOP6: {
        return f;
      }
      }
    }();
  }

  template <typename T1>
  static T1 instruction6_rec(const T1 f, const instruction6 i) {
    return [&](void) {
      switch (i) {
      case instruction6::NOP6: {
        return f;
      }
      }
    }();
  }

  struct state6 {
    unsigned int acc6;
  };

  static unsigned int cycles6(const std::shared_ptr<state6> &_x,
                              const instruction6 _x0);
  static unsigned int
  program_cycles6(const std::shared_ptr<state6> &s,
                  const std::shared_ptr<List<instruction6>> &prog);
  static inline const unsigned int singleton_cycles6 = program_cycles6(
      std::make_shared<state6>(state6{0u}),
      List<instruction6>::ctor::cons_(instruction6::NOP6,
                                      List<instruction6>::ctor::nil_()));
  static inline const unsigned int three_nop_cycles6 = program_cycles6(
      std::make_shared<state6>(state6{0u}),
      List<instruction6>::ctor::cons_(
          instruction6::NOP6,
          List<instruction6>::ctor::cons_(
              instruction6::NOP6,
              List<instruction6>::ctor::cons_(
                  instruction6::NOP6, List<instruction6>::ctor::nil_()))));
  static inline const std::pair<unsigned int, unsigned int>
      test_program_cycles =
          std::make_pair(singleton_cycles6, three_nop_cycles6);
  enum class instruction7 { NOP7 };

  template <typename T1>
  static T1 instruction7_rect(const T1 f, const instruction7 i) {
    return [&](void) {
      switch (i) {
      case instruction7::NOP7: {
        return f;
      }
      }
    }();
  }

  template <typename T1>
  static T1 instruction7_rec(const T1 f, const instruction7 i) {
    return [&](void) {
      switch (i) {
      case instruction7::NOP7: {
        return f;
      }
      }
    }();
  }

  struct state7 {
    unsigned int acc7;
  };

  static unsigned int cycles7(const std::shared_ptr<state7> &_x,
                              const instruction7 _x0);
  static unsigned int
  program_cycles7(const std::shared_ptr<state7> &s,
                  const std::shared_ptr<List<instruction7>> &prog);
  static inline const unsigned int test_program_cycles_single = program_cycles7(
      std::make_shared<state7>(state7{16u}),
      List<instruction7>::ctor::cons_(instruction7::NOP7,
                                      List<instruction7>::ctor::nil_()));
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
