#ifndef INCLUDED_INSTRUCTION_CYCLES
#define INCLUDED_INSTRUCTION_CYCLES

#include <any>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

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
  ~List() {
    std::vector<std::shared_ptr<List<A>>> _stack = {};
    auto _drain = [&](variant_t &_v) {
      if (auto *_alt = std::get_if<Cons>(&_v)) {
        if (_alt->l) {
          _stack.push_back(std::move(_alt->l));
        }
      }
    };
    _drain(v_mut());
    while (!_stack.empty()) {
      auto _cur = std::move(_stack.back());
      _stack.pop_back();
      if (_cur.use_count() == 1) {
        _drain(_cur->v_mut());
      }
    }
  }

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  template <typename F0>
    requires std::is_invocable_r_v<bool, F0 &, A &>
  bool forallb(F0 &&f) const {
    if (std::holds_alternative<typename List<A>::Nil>(this->v())) {
      return true;
    } else {
      const auto &[a0, a1] = std::get<typename List<A>::Cons>(this->v());
      return (f(a0) && a1->forallb(f));
    }
  }
};

struct InstructionCycles {
  struct state1 {
    uint64_t acc1;
    bool carry1;
    bool test_pin1;
  };

  struct instruction1 {
    // TYPES
    struct JCN1 {
      uint64_t a0;
      uint64_t a1;
    };

    struct NOP1 {};

    using variant_t = std::variant<JCN1, NOP1>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    instruction1() {}

    explicit instruction1(JCN1 _v) : v_(std::move(_v)) {}

    explicit instruction1(NOP1 _v) : v_(_v) {}

    static instruction1 jcn1(uint64_t a0, uint64_t a1) {
      return instruction1(JCN1{a0, a1});
    }

    static instruction1 nop1() { return instruction1(NOP1{}); }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    uint64_t cycles_jcn(const state1 &s) const {
      if (std::holds_alternative<typename instruction1::JCN1>(this->v())) {
        const auto &[a0, a1] = std::get<typename instruction1::JCN1>(this->v());
        uint64_t c1 = (UINT64_C(8) ? a0 / UINT64_C(8) : 0);
        uint64_t c2 =
            (UINT64_C(2) ? (UINT64_C(4) ? a0 / UINT64_C(4) : 0) % UINT64_C(2)
                         : (UINT64_C(4) ? a0 / UINT64_C(4) : 0));
        uint64_t c3 =
            (UINT64_C(2) ? (UINT64_C(2) ? a0 / UINT64_C(2) : 0) % UINT64_C(2)
                         : (UINT64_C(2) ? a0 / UINT64_C(2) : 0));
        uint64_t c4 = (UINT64_C(2) ? a0 % UINT64_C(2) : a0);
        bool base_cond = ((s.acc1 == UINT64_C(0) && c2 == UINT64_C(1)) ||
                          ((s.carry1 && c3 == UINT64_C(1)) ||
                           (!(s.test_pin1) && c4 == UINT64_C(1))));
        bool jump;
        if (c1 == UINT64_C(1)) {
          jump = !(base_cond);
        } else {
          jump = base_cond;
        }
        if (jump) {
          return UINT64_C(16);
        } else {
          return UINT64_C(8);
        }
      } else {
        return UINT64_C(8);
      }
    }

    template <typename T1, typename F0>
      requires std::is_invocable_r_v<T1, F0 &, uint64_t &, uint64_t &>
    T1 instruction1_rec(F0 &&f, T1 f0) const {
      if (std::holds_alternative<typename instruction1::JCN1>(this->v())) {
        const auto &[a0, a1] = std::get<typename instruction1::JCN1>(this->v());
        return f(a0, a1);
      } else {
        return f0;
      }
    }

    template <typename T1, typename F0>
      requires std::is_invocable_r_v<T1, F0 &, uint64_t &, uint64_t &>
    T1 instruction1_rect(F0 &&f, T1 f0) const {
      if (std::holds_alternative<typename instruction1::JCN1>(this->v())) {
        const auto &[a0, a1] = std::get<typename instruction1::JCN1>(this->v());
        return f(a0, a1);
      } else {
        return f0;
      }
    }
  };

  static inline const uint64_t test_cycles_jcn_not_taken =
      instruction1::jcn1(UINT64_C(4), UINT64_C(7))
          .cycles_jcn(state1{UINT64_C(1), false, true});

  struct instruction2 {
    // TYPES
    struct JMS2 {
      uint64_t a0;
    };

    struct NOP2 {};

    using variant_t = std::variant<JMS2, NOP2>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    instruction2() {}

    explicit instruction2(JMS2 _v) : v_(std::move(_v)) {}

    explicit instruction2(NOP2 _v) : v_(_v) {}

    static instruction2 jms2(uint64_t a0) { return instruction2(JMS2{a0}); }

    static instruction2 nop2() { return instruction2(NOP2{}); }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    template <typename T1, typename F0>
      requires std::is_invocable_r_v<T1, F0 &, uint64_t &>
    T1 instruction2_rec(F0 &&f, T1 f0) const {
      if (std::holds_alternative<typename instruction2::JMS2>(this->v())) {
        const auto &[a0] = std::get<typename instruction2::JMS2>(this->v());
        return f(a0);
      } else {
        return f0;
      }
    }

    template <typename T1, typename F0>
      requires std::is_invocable_r_v<T1, F0 &, uint64_t &>
    T1 instruction2_rect(F0 &&f, T1 f0) const {
      if (std::holds_alternative<typename instruction2::JMS2>(this->v())) {
        const auto &[a0] = std::get<typename instruction2::JMS2>(this->v());
        return f(a0);
      } else {
        return f0;
      }
    }
  };

  struct state2 {
    uint64_t acc2;
  };

  static uint64_t cycles_jms(const state2 &_x, const instruction2 &i);
  static inline const uint64_t test_cycles_jms_constant =
      cycles_jms(state2{UINT64_C(0)}, instruction2::jms2(UINT64_C(77)));
  enum class Instr3 {
    NOP3,
    ADD3,
    WRM3,
    FIM3,
    JMS3,
    JCNTAKEN3,
    JCNNOTTAKEN3,
    ISZTAKEN3,
    ISZZERO3
  };

  template <typename T1>
  static T1 instr3_rect(T1 f, T1 f0, T1 f1, T1 f2, T1 f3, T1 f4, T1 f5, T1 f6,
                        T1 f7, Instr3 i) {
    switch (i) {
    case Instr3::NOP3: {
      return f;
    }
    case Instr3::ADD3: {
      return f0;
    }
    case Instr3::WRM3: {
      return f1;
    }
    case Instr3::FIM3: {
      return f2;
    }
    case Instr3::JMS3: {
      return f3;
    }
    case Instr3::JCNTAKEN3: {
      return f4;
    }
    case Instr3::JCNNOTTAKEN3: {
      return f5;
    }
    case Instr3::ISZTAKEN3: {
      return f6;
    }
    case Instr3::ISZZERO3: {
      return f7;
    }
    default:
      std::unreachable();
    }
  }

  template <typename T1>
  static T1 instr3_rec(T1 f, T1 f0, T1 f1, T1 f2, T1 f3, T1 f4, T1 f5, T1 f6,
                       T1 f7, Instr3 i) {
    switch (i) {
    case Instr3::NOP3: {
      return f;
    }
    case Instr3::ADD3: {
      return f0;
    }
    case Instr3::WRM3: {
      return f1;
    }
    case Instr3::FIM3: {
      return f2;
    }
    case Instr3::JMS3: {
      return f3;
    }
    case Instr3::JCNTAKEN3: {
      return f4;
    }
    case Instr3::JCNNOTTAKEN3: {
      return f5;
    }
    case Instr3::ISZTAKEN3: {
      return f6;
    }
    case Instr3::ISZZERO3: {
      return f7;
    }
    default:
      std::unreachable();
    }
  }

  static uint64_t cycles_min(Instr3 i);
  static inline const List<Instr3> all_instrs3 = List<Instr3>::cons(
      Instr3::NOP3,
      List<Instr3>::cons(
          Instr3::ADD3,
          List<Instr3>::cons(
              Instr3::WRM3,
              List<Instr3>::cons(
                  Instr3::FIM3,
                  List<Instr3>::cons(
                      Instr3::JMS3,
                      List<Instr3>::cons(
                          Instr3::JCNTAKEN3,
                          List<Instr3>::cons(
                              Instr3::JCNNOTTAKEN3,
                              List<Instr3>::cons(
                                  Instr3::ISZTAKEN3,
                                  List<Instr3>::cons(
                                      Instr3::ISZZERO3,
                                      List<Instr3>::nil())))))))));
  static inline const bool test_min_cycles_per_instruction =
      all_instrs3.forallb(
          [](Instr3 i) { return UINT64_C(8) <= cycles_min(i); });
  enum class Instr4 {
    NOP4,
    ADD4,
    WRM4,
    FIM4,
    JMS4,
    JCNTAKEN4,
    JCNNOTTAKEN4,
    ISZTAKEN4,
    ISZZERO4
  };

  template <typename T1>
  static T1 instr4_rect(T1 f, T1 f0, T1 f1, T1 f2, T1 f3, T1 f4, T1 f5, T1 f6,
                        T1 f7, Instr4 i) {
    switch (i) {
    case Instr4::NOP4: {
      return f;
    }
    case Instr4::ADD4: {
      return f0;
    }
    case Instr4::WRM4: {
      return f1;
    }
    case Instr4::FIM4: {
      return f2;
    }
    case Instr4::JMS4: {
      return f3;
    }
    case Instr4::JCNTAKEN4: {
      return f4;
    }
    case Instr4::JCNNOTTAKEN4: {
      return f5;
    }
    case Instr4::ISZTAKEN4: {
      return f6;
    }
    case Instr4::ISZZERO4: {
      return f7;
    }
    default:
      std::unreachable();
    }
  }

  template <typename T1>
  static T1 instr4_rec(T1 f, T1 f0, T1 f1, T1 f2, T1 f3, T1 f4, T1 f5, T1 f6,
                       T1 f7, Instr4 i) {
    switch (i) {
    case Instr4::NOP4: {
      return f;
    }
    case Instr4::ADD4: {
      return f0;
    }
    case Instr4::WRM4: {
      return f1;
    }
    case Instr4::FIM4: {
      return f2;
    }
    case Instr4::JMS4: {
      return f3;
    }
    case Instr4::JCNTAKEN4: {
      return f4;
    }
    case Instr4::JCNNOTTAKEN4: {
      return f5;
    }
    case Instr4::ISZTAKEN4: {
      return f6;
    }
    case Instr4::ISZZERO4: {
      return f7;
    }
    default:
      std::unreachable();
    }
  }

  static uint64_t cycles_max(Instr4 i);
  static inline const List<Instr4> all_instrs4 = List<Instr4>::cons(
      Instr4::NOP4,
      List<Instr4>::cons(
          Instr4::ADD4,
          List<Instr4>::cons(
              Instr4::WRM4,
              List<Instr4>::cons(
                  Instr4::FIM4,
                  List<Instr4>::cons(
                      Instr4::JMS4,
                      List<Instr4>::cons(
                          Instr4::JCNTAKEN4,
                          List<Instr4>::cons(
                              Instr4::JCNNOTTAKEN4,
                              List<Instr4>::cons(
                                  Instr4::ISZTAKEN4,
                                  List<Instr4>::cons(
                                      Instr4::ISZZERO4,
                                      List<Instr4>::nil())))))))));
  static inline const bool test_max_cycles_per_instruction =
      all_instrs4.forallb(
          [](Instr4 i) { return cycles_max(i) <= UINT64_C(24); });

  struct state5 {
    uint64_t acc5;
    bool carry5;
    bool test5;
  };

  struct instruction5 {
    // TYPES
    struct NOP5 {};

    struct JCN5 {
      uint64_t a0;
    };

    struct INC5 {
      uint64_t a0;
    };

    using variant_t = std::variant<NOP5, JCN5, INC5>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    instruction5() {}

    explicit instruction5(NOP5 _v) : v_(_v) {}

    explicit instruction5(JCN5 _v) : v_(std::move(_v)) {}

    explicit instruction5(INC5 _v) : v_(std::move(_v)) {}

    static instruction5 nop5() { return instruction5(NOP5{}); }

    static instruction5 jcn5(uint64_t a0) { return instruction5(JCN5{a0}); }

    static instruction5 inc5(uint64_t a0) { return instruction5(INC5{a0}); }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    state5 execute5(state5 s) const {
      if (std::holds_alternative<typename instruction5::INC5>(this->v())) {
        return state5{(UINT64_C(16) ? (s.acc5 + UINT64_C(1)) % UINT64_C(16)
                                    : (s.acc5 + UINT64_C(1))),
                      s.carry5, s.test5};
      } else {
        return s;
      }
    }

    uint64_t cycles_sum(const state5 &s) const {
      if (std::holds_alternative<typename instruction5::JCN5>(this->v())) {
        const auto &[a0] = std::get<typename instruction5::JCN5>(this->v());
        if ((UINT64_C(8) ? a0 / UINT64_C(8) : 0) == UINT64_C(1)) {
          return UINT64_C(16);
        } else {
          if ((s.acc5 == UINT64_C(0) &&
               (UINT64_C(2)
                    ? (UINT64_C(4) ? a0 / UINT64_C(4) : 0) % UINT64_C(2)
                    : (UINT64_C(4) ? a0 / UINT64_C(4) : 0)) == UINT64_C(1))) {
            return UINT64_C(16);
          } else {
            return UINT64_C(8);
          }
        }
      } else {
        return UINT64_C(8);
      }
    }

    template <typename T1, typename F1, typename F2>
      requires std::is_invocable_r_v<T1, F1 &, uint64_t &> &&
               std::is_invocable_r_v<T1, F2 &, uint64_t &>
    T1 instruction5_rec(T1 f, F1 &&f0, F2 &&f1) const {
      if (std::holds_alternative<typename instruction5::NOP5>(this->v())) {
        return f;
      } else if (std::holds_alternative<typename instruction5::JCN5>(
                     this->v())) {
        const auto &[a0] = std::get<typename instruction5::JCN5>(this->v());
        return f0(a0);
      } else {
        const auto &[a0] = std::get<typename instruction5::INC5>(this->v());
        return f1(a0);
      }
    }

    template <typename T1, typename F1, typename F2>
      requires std::is_invocable_r_v<T1, F1 &, uint64_t &> &&
               std::is_invocable_r_v<T1, F2 &, uint64_t &>
    T1 instruction5_rect(T1 f, F1 &&f0, F2 &&f1) const {
      if (std::holds_alternative<typename instruction5::NOP5>(this->v())) {
        return f;
      } else if (std::holds_alternative<typename instruction5::JCN5>(
                     this->v())) {
        const auto &[a0] = std::get<typename instruction5::JCN5>(this->v());
        return f0(a0);
      } else {
        const auto &[a0] = std::get<typename instruction5::INC5>(this->v());
        return f1(a0);
      }
    }
  };

  static uint64_t program_cycles5(const state5 &s,
                                  const List<instruction5> &prog);
  static inline const uint64_t test_instruction_cycle_sum = program_cycles5(
      state5{UINT64_C(0), false, true},
      List<instruction5>::cons(
          instruction5::jcn5(UINT64_C(8)),
          List<instruction5>::cons(
              instruction5::inc5(UINT64_C(0)),
              List<instruction5>::cons(instruction5::nop5(),
                                       List<instruction5>::nil()))));
  enum class Instruction6 { NOP6 };

  template <typename T1> static T1 instruction6_rect(T1 f, Instruction6) {
    return f;
  }

  template <typename T1> static T1 instruction6_rec(T1 f, Instruction6) {
    return f;
  }

  struct state6 {
    uint64_t acc6;
  };

  static uint64_t cycles6(const state6 &_x, Instruction6 _x0);
  static uint64_t program_cycles6(const state6 &s,
                                  const List<Instruction6> &prog);
  static inline const uint64_t singleton_cycles6 = program_cycles6(
      state6{UINT64_C(0)},
      List<Instruction6>::cons(Instruction6::NOP6, List<Instruction6>::nil()));
  static inline const uint64_t three_nop_cycles6 = program_cycles6(
      state6{UINT64_C(0)},
      List<Instruction6>::cons(
          Instruction6::NOP6,
          List<Instruction6>::cons(
              Instruction6::NOP6,
              List<Instruction6>::cons(Instruction6::NOP6,
                                       List<Instruction6>::nil()))));
  static inline const std::pair<uint64_t, uint64_t> test_program_cycles =
      std::make_pair(singleton_cycles6, three_nop_cycles6);
  enum class Instruction7 { NOP7 };

  template <typename T1> static T1 instruction7_rect(T1 f, Instruction7) {
    return f;
  }

  template <typename T1> static T1 instruction7_rec(T1 f, Instruction7) {
    return f;
  }

  struct state7 {
    uint64_t acc7;
  };

  static uint64_t cycles7(const state7 &_x, Instruction7 _x0);
  static uint64_t program_cycles7(const state7 &s,
                                  const List<Instruction7> &prog);
  static inline const uint64_t test_program_cycles_single = program_cycles7(
      state7{UINT64_C(16)},
      List<Instruction7>::cons(Instruction7::NOP7, List<Instruction7>::nil()));
  static inline const std::pair<
      std::pair<
          std::pair<
              std::pair<std::pair<std::pair<uint64_t, uint64_t>, bool>, bool>,
              uint64_t>,
          std::pair<uint64_t, uint64_t>>,
      uint64_t>
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
