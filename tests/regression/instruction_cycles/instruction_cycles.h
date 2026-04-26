#ifndef INCLUDED_INSTRUCTION_CYCLES
#define INCLUDED_INSTRUCTION_CYCLES

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

template <typename T> struct is_unique_ptr : std::false_type {};

template <typename T>
struct is_unique_ptr<std::unique_ptr<T>> : std::true_type {
  using element_type = T;
};

template <typename T> auto clone_value(const T &x) { return x; }

template <typename T>
std::unique_ptr<T> clone_value(const std::unique_ptr<T> &x) {
  if constexpr (requires { x->clone(); }) {
    return x ? std::make_unique<T>(x->clone()) : nullptr;
  } else {
    return x ? std::make_unique<T>(*x) : nullptr;
  }
}

template <typename Target, typename Source>
Target clone_as_value(const Source &x) {
  using T = std::remove_cvref_t<Target>;
  using S = std::remove_cvref_t<Source>;
  if constexpr (requires(const S &s) {
                  s.has_value();
                  *s;
                }) {
    if (!x.has_value())
      return T{};
    using TInner = std::remove_cvref_t<decltype(*std::declval<const T &>())>;
    return T{clone_as_value<TInner>(*x)};
  } else if constexpr (std::is_same_v<T, S>) {
    if constexpr (is_unique_ptr<T>::value) {
      return clone_value(x);
    } else if constexpr (requires { x.clone(); }) {
      return x.clone();
    } else {
      return x;
    }
  } else if constexpr (is_unique_ptr<S>::value) {
    if (!x)
      return T{};
    return clone_as_value<T>(*x);
  } else if constexpr (is_unique_ptr<T>::value) {
    using Inner = typename is_unique_ptr<T>::element_type;
    return std::make_unique<Inner>(clone_as_value<Inner>(x));
  } else {
    return T(x);
  }
}

template <typename t_A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    t_A d_a0;
    std::unique_ptr<List<t_A>> d_a1;
  };

  using variant_t = std::variant<Nil, Cons>;
  using crane_element_type = t_A;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  List() {}

  explicit List(Nil _v) : d_v_(_v) {}

  explicit List(Cons _v) : d_v_(std::move(_v)) {}

  List(const List<t_A> &_other) : d_v_(std::move(_other.clone().d_v_)) {}

  List(List<t_A> &&_other) : d_v_(std::move(_other.d_v_)) {}

  __attribute__((pure)) List<t_A> &operator=(const List<t_A> &_other) {
    d_v_ = std::move(_other.clone().d_v_);
    return *this;
  }

  __attribute__((pure)) List<t_A> &operator=(List<t_A> &&_other) {
    d_v_ = std::move(_other.d_v_);
    return *this;
  }

  // ACCESSORS
  __attribute__((pure)) List<t_A> clone() const {
    auto &&_sv = *(this);
    if (std::holds_alternative<Nil>(_sv.v())) {
      return List<t_A>(Nil{});
    } else {
      const auto &[d_a0, d_a1] = std::get<Cons>(_sv.v());
      return List<t_A>(Cons{clone_value(d_a0), clone_value(d_a1)});
    }
  }

  // CREATORS
  template <typename _U> explicit List(const List<_U> &_other) {
    if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
      d_v_ = Nil{};
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<_U>::Cons>(_other.v());
      d_v_ = Cons{clone_as_value<t_A>(d_a0),
                  d_a1 ? std::make_unique<List<t_A>>(*d_a1) : nullptr};
    }
  }

  __attribute__((pure)) static List<t_A> nil() { return List(Nil{}); }

  __attribute__((pure)) static List<t_A> cons(t_A a0, const List<t_A> &a1) {
    return List(Cons{std::move(a0), std::make_unique<List<t_A>>(a1)});
  }

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) List<t_A> *operator->() { return this; }

  __attribute__((pure)) const List<t_A> *operator->() const { return this; }

  __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

  __attribute__((pure)) bool operator==(std::nullptr_t) const { return false; }

  // MANIPULATORS
  void reset() { *this = List<t_A>(); }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }

  template <MapsTo<bool, t_A> F0>
  __attribute__((pure)) bool forallb(F0 &&f) const {
    auto &&_sv = *(this);
    if (std::holds_alternative<typename List<t_A>::Nil>(_sv.v())) {
      return true;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<t_A>::Cons>(_sv.v());
      return (f(d_a0) && (*(d_a1)).forallb(f));
    }
  }
};

struct InstructionCycles {
  struct state1 {
    unsigned int acc1;
    bool carry1;
    bool test_pin1;

    __attribute__((pure)) state1 *operator->() { return this; }

    __attribute__((pure)) const state1 *operator->() const { return this; }

    // ACCESSORS
    __attribute__((pure)) state1 clone() const {
      return state1{(*(this)).acc1, (*(this)).carry1, (*(this)).test_pin1};
    }
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

  public:
    // CREATORS
    instruction1() {}

    explicit instruction1(JCN1 _v) : d_v_(std::move(_v)) {}

    explicit instruction1(NOP1 _v) : d_v_(_v) {}

    instruction1(const instruction1 &_other)
        : d_v_(std::move(_other.clone().d_v_)) {}

    instruction1(instruction1 &&_other) : d_v_(std::move(_other.d_v_)) {}

    __attribute__((pure)) instruction1 &operator=(const instruction1 &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    __attribute__((pure)) instruction1 &operator=(instruction1 &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) instruction1 clone() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<JCN1>(_sv.v())) {
        const auto &[d_a0, d_a1] = std::get<JCN1>(_sv.v());
        return instruction1(JCN1{d_a0, d_a1});
      } else {
        return instruction1(NOP1{});
      }
    }

    // CREATORS
    __attribute__((pure)) static instruction1 jcn1(unsigned int a0,
                                                   unsigned int a1) {
      return instruction1(JCN1{std::move(a0), std::move(a1)});
    }

    constexpr static instruction1 nop1() { return instruction1(NOP1{}); }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) instruction1 *operator->() { return this; }

    __attribute__((pure)) const instruction1 *operator->() const {
      return this;
    }

    __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

    __attribute__((pure)) bool operator==(std::nullptr_t) const {
      return false;
    }

    // MANIPULATORS
    void reset() { *this = instruction1(); }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    __attribute__((pure)) unsigned int cycles_jcn(const state1 &s) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename instruction1::JCN1>(_sv.v())) {
        const auto &[d_a0, d_a1] =
            std::get<typename instruction1::JCN1>(_sv.v());
        unsigned int c1 = (8u ? d_a0 / 8u : 0);
        unsigned int c2 =
            (2u ? (4u ? d_a0 / 4u : 0) % 2u : (4u ? d_a0 / 4u : 0));
        unsigned int c3 =
            (2u ? (2u ? d_a0 / 2u : 0) % 2u : (2u ? d_a0 / 2u : 0));
        unsigned int c4 = (2u ? d_a0 % 2u : d_a0);
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

    template <typename T1, MapsTo<T1, unsigned int, unsigned int> F0>
    T1 instruction1_rec(F0 &&f, const T1 f0) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename instruction1::JCN1>(_sv.v())) {
        const auto &[d_a0, d_a1] =
            std::get<typename instruction1::JCN1>(_sv.v());
        return f(d_a0, d_a1);
      } else {
        return f0;
      }
    }

    template <typename T1, MapsTo<T1, unsigned int, unsigned int> F0>
    T1 instruction1_rect(F0 &&f, const T1 f0) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename instruction1::JCN1>(_sv.v())) {
        const auto &[d_a0, d_a1] =
            std::get<typename instruction1::JCN1>(_sv.v());
        return f(d_a0, d_a1);
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
      unsigned int d_a0;
    };

    struct NOP2 {};

    using variant_t = std::variant<JMS2, NOP2>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    instruction2() {}

    explicit instruction2(JMS2 _v) : d_v_(std::move(_v)) {}

    explicit instruction2(NOP2 _v) : d_v_(_v) {}

    instruction2(const instruction2 &_other)
        : d_v_(std::move(_other.clone().d_v_)) {}

    instruction2(instruction2 &&_other) : d_v_(std::move(_other.d_v_)) {}

    __attribute__((pure)) instruction2 &operator=(const instruction2 &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    __attribute__((pure)) instruction2 &operator=(instruction2 &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) instruction2 clone() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<JMS2>(_sv.v())) {
        const auto &[d_a0] = std::get<JMS2>(_sv.v());
        return instruction2(JMS2{d_a0});
      } else {
        return instruction2(NOP2{});
      }
    }

    // CREATORS
    __attribute__((pure)) static instruction2 jms2(unsigned int a0) {
      return instruction2(JMS2{std::move(a0)});
    }

    constexpr static instruction2 nop2() { return instruction2(NOP2{}); }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) instruction2 *operator->() { return this; }

    __attribute__((pure)) const instruction2 *operator->() const {
      return this;
    }

    __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

    __attribute__((pure)) bool operator==(std::nullptr_t) const {
      return false;
    }

    // MANIPULATORS
    void reset() { *this = instruction2(); }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    template <typename T1, MapsTo<T1, unsigned int> F0>
    T1 instruction2_rec(F0 &&f, const T1 f0) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename instruction2::JMS2>(_sv.v())) {
        const auto &[d_a0] = std::get<typename instruction2::JMS2>(_sv.v());
        return f(d_a0);
      } else {
        return f0;
      }
    }

    template <typename T1, MapsTo<T1, unsigned int> F0>
    T1 instruction2_rect(F0 &&f, const T1 f0) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename instruction2::JMS2>(_sv.v())) {
        const auto &[d_a0] = std::get<typename instruction2::JMS2>(_sv.v());
        return f(d_a0);
      } else {
        return f0;
      }
    }
  };

  struct state2 {
    unsigned int acc2;

    __attribute__((pure)) state2 *operator->() { return this; }

    __attribute__((pure)) const state2 *operator->() const { return this; }

    // ACCESSORS
    __attribute__((pure)) state2 clone() const {
      return state2{(*(this)).acc2};
    }
  };

  __attribute__((pure)) static unsigned int cycles_jms(const state2 &_x,
                                                       const instruction2 &i);
  static inline const unsigned int test_cycles_jms_constant =
      cycles_jms(state2{0u}, instruction2::jms2(77u));
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
    default:
      std::unreachable();
    }
  }

  template <typename T1>
  static T1 instr3_rec(const T1 f, const T1 f0, const T1 f1, const T1 f2,
                       const T1 f3, const T1 f4, const T1 f5, const T1 f6,
                       const T1 f7, const Instr3 i) {
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
    default:
      std::unreachable();
    }
  }

  __attribute__((pure)) static unsigned int cycles_min(const Instr3 i);
  static inline const List<Instr3> all_instrs3 = List<Instr3>::cons(
      Instr3::e_NOP3,
      List<Instr3>::cons(
          Instr3::e_ADD3,
          List<Instr3>::cons(
              Instr3::e_WRM3,
              List<Instr3>::cons(
                  Instr3::e_FIM3,
                  List<Instr3>::cons(
                      Instr3::e_JMS3,
                      List<Instr3>::cons(
                          Instr3::e_JCNTAKEN3,
                          List<Instr3>::cons(
                              Instr3::e_JCNNOTTAKEN3,
                              List<Instr3>::cons(
                                  Instr3::e_ISZTAKEN3,
                                  List<Instr3>::cons(
                                      Instr3::e_ISZZERO3,
                                      List<Instr3>::nil())))))))));
  static inline const bool test_min_cycles_per_instruction =
      all_instrs3.forallb([](const Instr3 i) { return 8u <= cycles_min(i); });
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
    default:
      std::unreachable();
    }
  }

  template <typename T1>
  static T1 instr4_rec(const T1 f, const T1 f0, const T1 f1, const T1 f2,
                       const T1 f3, const T1 f4, const T1 f5, const T1 f6,
                       const T1 f7, const Instr4 i) {
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
    default:
      std::unreachable();
    }
  }

  __attribute__((pure)) static unsigned int cycles_max(const Instr4 i);
  static inline const List<Instr4> all_instrs4 = List<Instr4>::cons(
      Instr4::e_NOP4,
      List<Instr4>::cons(
          Instr4::e_ADD4,
          List<Instr4>::cons(
              Instr4::e_WRM4,
              List<Instr4>::cons(
                  Instr4::e_FIM4,
                  List<Instr4>::cons(
                      Instr4::e_JMS4,
                      List<Instr4>::cons(
                          Instr4::e_JCNTAKEN4,
                          List<Instr4>::cons(
                              Instr4::e_JCNNOTTAKEN4,
                              List<Instr4>::cons(
                                  Instr4::e_ISZTAKEN4,
                                  List<Instr4>::cons(
                                      Instr4::e_ISZZERO4,
                                      List<Instr4>::nil())))))))));
  static inline const bool test_max_cycles_per_instruction =
      all_instrs4.forallb([](const Instr4 i) { return cycles_max(i) <= 24u; });

  struct state5 {
    unsigned int acc5;
    bool carry5;
    bool test5;

    __attribute__((pure)) state5 *operator->() { return this; }

    __attribute__((pure)) const state5 *operator->() const { return this; }

    // ACCESSORS
    __attribute__((pure)) state5 clone() const {
      return state5{(*(this)).acc5, (*(this)).carry5, (*(this)).test5};
    }
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

  public:
    // CREATORS
    instruction5() {}

    explicit instruction5(NOP5 _v) : d_v_(_v) {}

    explicit instruction5(JCN5 _v) : d_v_(std::move(_v)) {}

    explicit instruction5(INC5 _v) : d_v_(std::move(_v)) {}

    instruction5(const instruction5 &_other)
        : d_v_(std::move(_other.clone().d_v_)) {}

    instruction5(instruction5 &&_other) : d_v_(std::move(_other.d_v_)) {}

    __attribute__((pure)) instruction5 &operator=(const instruction5 &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    __attribute__((pure)) instruction5 &operator=(instruction5 &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) instruction5 clone() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<NOP5>(_sv.v())) {
        return instruction5(NOP5{});
      } else if (std::holds_alternative<JCN5>(_sv.v())) {
        const auto &[d_a0] = std::get<JCN5>(_sv.v());
        return instruction5(JCN5{d_a0});
      } else {
        const auto &[d_a0] = std::get<INC5>(_sv.v());
        return instruction5(INC5{d_a0});
      }
    }

    // CREATORS
    constexpr static instruction5 nop5() { return instruction5(NOP5{}); }

    __attribute__((pure)) static instruction5 jcn5(unsigned int a0) {
      return instruction5(JCN5{std::move(a0)});
    }

    __attribute__((pure)) static instruction5 inc5(unsigned int a0) {
      return instruction5(INC5{std::move(a0)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) instruction5 *operator->() { return this; }

    __attribute__((pure)) const instruction5 *operator->() const {
      return this;
    }

    __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

    __attribute__((pure)) bool operator==(std::nullptr_t) const {
      return false;
    }

    // MANIPULATORS
    void reset() { *this = instruction5(); }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    __attribute__((pure)) state5 execute5(state5 s) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename instruction5::INC5>(_sv.v())) {
        return state5{(16u ? (s.acc5 + 1u) % 16u : (s.acc5 + 1u)), s.carry5,
                      s.test5};
      } else {
        return s;
      }
    }

    __attribute__((pure)) unsigned int cycles_sum(const state5 &s) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename instruction5::JCN5>(_sv.v())) {
        const auto &[d_a0] = std::get<typename instruction5::JCN5>(_sv.v());
        if ((8u ? d_a0 / 8u : 0) == 1u) {
          return 16u;
        } else {
          if ((s.acc5 == 0u &&
               (2u ? (4u ? d_a0 / 4u : 0) % 2u : (4u ? d_a0 / 4u : 0)) == 1u)) {
            return 16u;
          } else {
            return 8u;
          }
        }
      } else {
        return 8u;
      }
    }

    template <typename T1, MapsTo<T1, unsigned int> F1,
              MapsTo<T1, unsigned int> F2>
    T1 instruction5_rec(const T1 f, F1 &&f0, F2 &&f1) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename instruction5::NOP5>(_sv.v())) {
        return f;
      } else if (std::holds_alternative<typename instruction5::JCN5>(_sv.v())) {
        const auto &[d_a0] = std::get<typename instruction5::JCN5>(_sv.v());
        return f0(d_a0);
      } else {
        const auto &[d_a0] = std::get<typename instruction5::INC5>(_sv.v());
        return f1(d_a0);
      }
    }

    template <typename T1, MapsTo<T1, unsigned int> F1,
              MapsTo<T1, unsigned int> F2>
    T1 instruction5_rect(const T1 f, F1 &&f0, F2 &&f1) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename instruction5::NOP5>(_sv.v())) {
        return f;
      } else if (std::holds_alternative<typename instruction5::JCN5>(_sv.v())) {
        const auto &[d_a0] = std::get<typename instruction5::JCN5>(_sv.v());
        return f0(d_a0);
      } else {
        const auto &[d_a0] = std::get<typename instruction5::INC5>(_sv.v());
        return f1(d_a0);
      }
    }
  };

  __attribute__((pure)) static unsigned int
  program_cycles5(const state5 &s, const List<instruction5> &prog);
  static inline const unsigned int test_instruction_cycle_sum = program_cycles5(
      state5{0u, false, true},
      List<instruction5>::cons(
          instruction5::jcn5(8u),
          List<instruction5>::cons(
              instruction5::inc5(0u),
              List<instruction5>::cons(instruction5::nop5(),
                                       List<instruction5>::nil()))));
  enum class Instruction6 { e_NOP6 };

  template <typename T1>
  static T1 instruction6_rect(const T1 f, const Instruction6) {
    return f;
  }

  template <typename T1>
  static T1 instruction6_rec(const T1 f, const Instruction6) {
    return f;
  }

  struct state6 {
    unsigned int acc6;

    __attribute__((pure)) state6 *operator->() { return this; }

    __attribute__((pure)) const state6 *operator->() const { return this; }

    // ACCESSORS
    __attribute__((pure)) state6 clone() const {
      return state6{(*(this)).acc6};
    }
  };

  __attribute__((pure)) static unsigned int cycles6(const state6 &_x,
                                                    const Instruction6 _x0);
  __attribute__((pure)) static unsigned int
  program_cycles6(const state6 &s, const List<Instruction6> &prog);
  static inline const unsigned int singleton_cycles6 = program_cycles6(
      state6{0u}, List<Instruction6>::cons(Instruction6::e_NOP6,
                                           List<Instruction6>::nil()));
  static inline const unsigned int three_nop_cycles6 = program_cycles6(
      state6{0u},
      List<Instruction6>::cons(
          Instruction6::e_NOP6,
          List<Instruction6>::cons(
              Instruction6::e_NOP6,
              List<Instruction6>::cons(Instruction6::e_NOP6,
                                       List<Instruction6>::nil()))));
  static inline const std::pair<unsigned int, unsigned int>
      test_program_cycles =
          std::make_pair(singleton_cycles6, three_nop_cycles6);
  enum class Instruction7 { e_NOP7 };

  template <typename T1>
  static T1 instruction7_rect(const T1 f, const Instruction7) {
    return f;
  }

  template <typename T1>
  static T1 instruction7_rec(const T1 f, const Instruction7) {
    return f;
  }

  struct state7 {
    unsigned int acc7;

    __attribute__((pure)) state7 *operator->() { return this; }

    __attribute__((pure)) const state7 *operator->() const { return this; }

    // ACCESSORS
    __attribute__((pure)) state7 clone() const {
      return state7{(*(this)).acc7};
    }
  };

  __attribute__((pure)) static unsigned int cycles7(const state7 &_x,
                                                    const Instruction7 _x0);
  __attribute__((pure)) static unsigned int
  program_cycles7(const state7 &s, const List<Instruction7> &prog);
  static inline const unsigned int test_program_cycles_single = program_cycles7(
      state7{16u}, List<Instruction7>::cons(Instruction7::e_NOP7,
                                            List<Instruction7>::nil()));
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
