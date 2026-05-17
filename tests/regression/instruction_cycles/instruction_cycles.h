#ifndef INCLUDED_INSTRUCTION_CYCLES
#define INCLUDED_INSTRUCTION_CYCLES

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

template <typename A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    A a0;
    std::unique_ptr<List<A>> a1;
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

  List(const List<A> &_other) : v_(std::move(_other.clone().v_)) {}

  List(List<A> &&_other) noexcept : v_(std::move(_other.v_)) {}

  List<A> &operator=(const List<A> &_other) {
    v_ = std::move(_other.clone().v_);
    return *this;
  }

  List<A> &operator=(List<A> &&_other) noexcept {
    v_ = std::move(_other.v_);
    return *this;
  }

  // ACCESSORS
  List<A> clone() const {
    List<A> _out{};

    struct _CloneFrame {
      const List<A> *_src;
      List<A> *_dst;
    };

    std::vector<_CloneFrame> _stack{};
    _stack.reserve(8);
    _stack.push_back({this, &_out});
    while (!_stack.empty()) {
      auto _frame = _stack.back();
      _stack.pop_back();
      const List<A> *_src = _frame._src;
      List<A> *_dst = _frame._dst;
      if (std::holds_alternative<Nil>(_src->v())) {
        _dst->v_ = Nil{};
      } else {
        const auto &_alt = std::get<Cons>(_src->v());
        _dst->v_ =
            Cons{_alt.a0, _alt.a1 ? std::make_unique<List<A>>() : nullptr};
        auto &_dst_alt = std::get<Cons>(_dst->v_);
        if (_alt.a1) {
          _stack.push_back({_alt.a1.get(), _dst_alt.a1.get()});
        }
      }
    }
    return _out;
  }

  // CREATORS
  template <typename _U> explicit List(const List<_U> &_other) {
    if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
      this->v_ = Nil{};
    } else {
      const auto &[a0, a1] = std::get<typename List<_U>::Cons>(_other.v());
      this->v_ = Cons{A(a0), a1 ? std::make_unique<List<A>>(*a1) : nullptr};
    }
  }

  static List<A> nil() { return List(Nil{}); }

  static List<A> cons(A a0, List<A> a1) {
    return List(Cons{std::move(a0), std::make_unique<List<A>>(std::move(a1))});
  }

  // MANIPULATORS
  ~List() {
    std::vector<std::unique_ptr<List<A>>> _stack{};
    _stack.reserve(8);
    auto _drain = [&](List<A> &_node) {
      if (std::holds_alternative<Cons>(_node.v_)) {
        auto &_alt = std::get<Cons>(_node.v_);
        if (_alt.a1) {
          _stack.push_back(std::move(_alt.a1));
        }
      }
    };
    _drain(*this);
    while (!_stack.empty()) {
      auto _node = std::move(_stack.back());
      _stack.pop_back();
      if (_node) {
        _drain(*_node);
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
      return (f(a0) && (*a1).forallb(f));
    }
  }
};

struct InstructionCycles {
  struct state1 {
    unsigned int acc1;
    bool carry1;
    bool test_pin1;

    // ACCESSORS
    state1 clone() const {
      return state1{(*this).acc1, (*this).carry1, (*this).test_pin1};
    }
  };

  struct instruction1 {
    // TYPES
    struct JCN1 {
      unsigned int a0;
      unsigned int a1;
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

    instruction1(const instruction1 &_other)
        : v_(std::move(_other.clone().v_)) {}

    instruction1(instruction1 &&_other) noexcept : v_(std::move(_other.v_)) {}

    instruction1 &operator=(const instruction1 &_other) {
      v_ = std::move(_other.clone().v_);
      return *this;
    }

    instruction1 &operator=(instruction1 &&_other) noexcept {
      v_ = std::move(_other.v_);
      return *this;
    }

    // ACCESSORS
    instruction1 clone() const {
      if (std::holds_alternative<JCN1>(this->v())) {
        const auto &[a0, a1] = std::get<JCN1>(this->v());
        return instruction1(JCN1{a0, a1});
      } else {
        return instruction1(NOP1{});
      }
    }

    // CREATORS
    static instruction1 jcn1(unsigned int a0, unsigned int a1) {
      return instruction1(JCN1{a0, a1});
    }

    static instruction1 nop1() { return instruction1(NOP1{}); }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    unsigned int cycles_jcn(const state1 &s) const {
      if (std::holds_alternative<typename instruction1::JCN1>(this->v())) {
        const auto &[a0, a1] = std::get<typename instruction1::JCN1>(this->v());
        unsigned int c1 = (8u ? a0 / 8u : 0);
        unsigned int c2 = (2u ? (4u ? a0 / 4u : 0) % 2u : (4u ? a0 / 4u : 0));
        unsigned int c3 = (2u ? (2u ? a0 / 2u : 0) % 2u : (2u ? a0 / 2u : 0));
        unsigned int c4 = (2u ? a0 % 2u : a0);
        bool base_cond =
            ((s.acc1 == 0u && c2 == 1u) ||
             ((s.carry1 && c3 == 1u) || (!(s.test_pin1) && c4 == 1u)));
        bool jump;
        if (c1 == 1u) {
          jump = !(base_cond);
        } else {
          jump = base_cond;
        }
        if (jump) {
          return 16u;
        } else {
          return 8u;
        }
      } else {
        return 8u;
      }
    }

    template <typename T1, typename F0>
      requires std::is_invocable_r_v<T1, F0 &, unsigned int &, unsigned int &>
    T1 instruction1_rec(F0 &&f, T1 f0) const {
      if (std::holds_alternative<typename instruction1::JCN1>(this->v())) {
        const auto &[a0, a1] = std::get<typename instruction1::JCN1>(this->v());
        return f(a0, a1);
      } else {
        return f0;
      }
    }

    template <typename T1, typename F0>
      requires std::is_invocable_r_v<T1, F0 &, unsigned int &, unsigned int &>
    T1 instruction1_rect(F0 &&f, T1 f0) const {
      if (std::holds_alternative<typename instruction1::JCN1>(this->v())) {
        const auto &[a0, a1] = std::get<typename instruction1::JCN1>(this->v());
        return f(a0, a1);
      } else {
        return f0;
      }
    }
  };

  static inline const unsigned int test_cycles_jcn_not_taken =
      instruction1::jcn1(4u, 7u).cycles_jcn(state1{1u, false, true});

  struct instruction2 {
    // TYPES
    struct JMS2 {
      unsigned int a0;
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

    instruction2(const instruction2 &_other)
        : v_(std::move(_other.clone().v_)) {}

    instruction2(instruction2 &&_other) noexcept : v_(std::move(_other.v_)) {}

    instruction2 &operator=(const instruction2 &_other) {
      v_ = std::move(_other.clone().v_);
      return *this;
    }

    instruction2 &operator=(instruction2 &&_other) noexcept {
      v_ = std::move(_other.v_);
      return *this;
    }

    // ACCESSORS
    instruction2 clone() const {
      if (std::holds_alternative<JMS2>(this->v())) {
        const auto &[a0] = std::get<JMS2>(this->v());
        return instruction2(JMS2{a0});
      } else {
        return instruction2(NOP2{});
      }
    }

    // CREATORS
    static instruction2 jms2(unsigned int a0) { return instruction2(JMS2{a0}); }

    static instruction2 nop2() { return instruction2(NOP2{}); }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    template <typename T1, typename F0>
      requires std::is_invocable_r_v<T1, F0 &, unsigned int &>
    T1 instruction2_rec(F0 &&f, T1 f0) const {
      if (std::holds_alternative<typename instruction2::JMS2>(this->v())) {
        const auto &[a0] = std::get<typename instruction2::JMS2>(this->v());
        return f(a0);
      } else {
        return f0;
      }
    }

    template <typename T1, typename F0>
      requires std::is_invocable_r_v<T1, F0 &, unsigned int &>
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
    unsigned int acc2;

    // ACCESSORS
    state2 clone() const { return state2{(*this).acc2}; }
  };

  static unsigned int cycles_jms(const state2 &_x, const instruction2 &i);
  static inline const unsigned int test_cycles_jms_constant =
      cycles_jms(state2{0u}, instruction2::jms2(77u));
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

  static unsigned int cycles_min(Instr3 i);
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
      all_instrs3.forallb([](Instr3 i) { return 8u <= cycles_min(i); });
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

  static unsigned int cycles_max(Instr4 i);
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
      all_instrs4.forallb([](Instr4 i) { return cycles_max(i) <= 24u; });

  struct state5 {
    unsigned int acc5;
    bool carry5;
    bool test5;

    // ACCESSORS
    state5 clone() const {
      return state5{(*this).acc5, (*this).carry5, (*this).test5};
    }
  };

  struct instruction5 {
    // TYPES
    struct NOP5 {};

    struct JCN5 {
      unsigned int a0;
    };

    struct INC5 {
      unsigned int a0;
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

    instruction5(const instruction5 &_other)
        : v_(std::move(_other.clone().v_)) {}

    instruction5(instruction5 &&_other) noexcept : v_(std::move(_other.v_)) {}

    instruction5 &operator=(const instruction5 &_other) {
      v_ = std::move(_other.clone().v_);
      return *this;
    }

    instruction5 &operator=(instruction5 &&_other) noexcept {
      v_ = std::move(_other.v_);
      return *this;
    }

    // ACCESSORS
    instruction5 clone() const {
      if (std::holds_alternative<NOP5>(this->v())) {
        return instruction5(NOP5{});
      } else if (std::holds_alternative<JCN5>(this->v())) {
        const auto &[a0] = std::get<JCN5>(this->v());
        return instruction5(JCN5{a0});
      } else {
        const auto &[a0] = std::get<INC5>(this->v());
        return instruction5(INC5{a0});
      }
    }

    // CREATORS
    static instruction5 nop5() { return instruction5(NOP5{}); }

    static instruction5 jcn5(unsigned int a0) { return instruction5(JCN5{a0}); }

    static instruction5 inc5(unsigned int a0) { return instruction5(INC5{a0}); }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    state5 execute5(state5 s) const {
      if (std::holds_alternative<typename instruction5::INC5>(this->v())) {
        return state5{(16u ? (s.acc5 + 1u) % 16u : (s.acc5 + 1u)), s.carry5,
                      s.test5};
      } else {
        return s;
      }
    }

    unsigned int cycles_sum(const state5 &s) const {
      if (std::holds_alternative<typename instruction5::JCN5>(this->v())) {
        const auto &[a0] = std::get<typename instruction5::JCN5>(this->v());
        if ((8u ? a0 / 8u : 0) == 1u) {
          return 16u;
        } else {
          if ((s.acc5 == 0u &&
               (2u ? (4u ? a0 / 4u : 0) % 2u : (4u ? a0 / 4u : 0)) == 1u)) {
            return 16u;
          } else {
            return 8u;
          }
        }
      } else {
        return 8u;
      }
    }

    template <typename T1, typename F1, typename F2>
      requires std::is_invocable_r_v<T1, F1 &, unsigned int &> &&
               std::is_invocable_r_v<T1, F2 &, unsigned int &>
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
      requires std::is_invocable_r_v<T1, F1 &, unsigned int &> &&
               std::is_invocable_r_v<T1, F2 &, unsigned int &>
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

  static unsigned int program_cycles5(const state5 &s,
                                      const List<instruction5> &prog);
  static inline const unsigned int test_instruction_cycle_sum = program_cycles5(
      state5{0u, false, true},
      List<instruction5>::cons(
          instruction5::jcn5(8u),
          List<instruction5>::cons(
              instruction5::inc5(0u),
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
    unsigned int acc6;

    // ACCESSORS
    state6 clone() const { return state6{(*this).acc6}; }
  };

  static unsigned int cycles6(const state6 &_x, Instruction6 _x0);
  static unsigned int program_cycles6(const state6 &s,
                                      const List<Instruction6> &prog);
  static inline const unsigned int singleton_cycles6 = program_cycles6(
      state6{0u},
      List<Instruction6>::cons(Instruction6::NOP6, List<Instruction6>::nil()));
  static inline const unsigned int three_nop_cycles6 = program_cycles6(
      state6{0u}, List<Instruction6>::cons(
                      Instruction6::NOP6,
                      List<Instruction6>::cons(
                          Instruction6::NOP6,
                          List<Instruction6>::cons(
                              Instruction6::NOP6, List<Instruction6>::nil()))));
  static inline const std::pair<unsigned int, unsigned int>
      test_program_cycles =
          std::make_pair(singleton_cycles6, three_nop_cycles6);
  enum class Instruction7 { NOP7 };

  template <typename T1> static T1 instruction7_rect(T1 f, Instruction7) {
    return f;
  }

  template <typename T1> static T1 instruction7_rec(T1 f, Instruction7) {
    return f;
  }

  struct state7 {
    unsigned int acc7;

    // ACCESSORS
    state7 clone() const { return state7{(*this).acc7}; }
  };

  static unsigned int cycles7(const state7 &_x, Instruction7 _x0);
  static unsigned int program_cycles7(const state7 &s,
                                      const List<Instruction7> &prog);
  static inline const unsigned int test_program_cycles_single = program_cycles7(
      state7{16u},
      List<Instruction7>::cons(Instruction7::NOP7, List<Instruction7>::nil()));
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
