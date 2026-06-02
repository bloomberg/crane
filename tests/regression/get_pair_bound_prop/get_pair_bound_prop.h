#ifndef INCLUDED_GET_PAIR_BOUND_PROP
#define INCLUDED_GET_PAIR_BOUND_PROP

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

  List<A> skipn(uint64_t n) const {
    if (n <= 0) {
      return std::move(*this);
    } else {
      uint64_t n0 = n - 1;
      if (std::holds_alternative<typename List<A>::Nil>(this->v())) {
        return List<A>::nil();
      } else {
        auto &[a0, a1] = std::get<typename List<A>::Cons>(this->v());
        return a1->skipn(n0);
      }
    }
  }

  List<A> firstn(uint64_t n) const {
    if (n <= 0) {
      return List<A>::nil();
    } else {
      uint64_t n0 = n - 1;
      if (std::holds_alternative<typename List<A>::Nil>(this->v())) {
        return List<A>::nil();
      } else {
        const auto &[a0, a1] = std::get<typename List<A>::Cons>(this->v());
        return List<A>::cons(a0, a1->firstn(n0));
      }
    }
  }
};

struct ListDef {
  template <typename T1>
  static T1 nth(uint64_t n, const List<T1> &l, T1 default0);
};

struct GetPairBoundProp {
  template <typename T1>
  static List<T1> update_nth(uint64_t n, T1 x, const List<T1> &l) {
    if (n <= 0) {
      if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
        return List<T1>::nil();
      } else {
        const auto &[a0, a1] = std::get<typename List<T1>::Cons>(l.v());
        return List<T1>::cons(x, *a1);
      }
    } else {
      uint64_t n_ = n - 1;
      if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
        return List<T1>::nil();
      } else {
        const auto &[a00, a10] = std::get<typename List<T1>::Cons>(l.v());
        return List<T1>::cons(a00, update_nth<T1>(n_, x, *a10));
      }
    }
  }

  struct state {
    uint64_t ex_acc;
    List<uint64_t> ex_regs;
    bool ex_carry;
    uint64_t ex_pc;
    List<uint64_t> ex_stack;
    uint64_t ex_pair_bus;
    List<uint64_t> ex_ports;
  };

  static uint64_t get_reg(const state &s, uint64_t r);
  static List<uint64_t> set_reg(const state &s, uint64_t r, uint64_t v);
  static uint64_t pair_base(uint64_t r);
  static uint64_t get_pair(const state &s, uint64_t r);
  static List<uint64_t> set_pair(const state &s, uint64_t r, uint64_t v);
  static List<uint64_t> push_return(const state &s, uint64_t ret);

  struct instr {
    // TYPES
    struct NOP {};

    struct LDM {
      uint64_t n;
    };

    struct LD {
      uint64_t r;
    };

    struct XCH {
      uint64_t r;
    };

    struct INC {
      uint64_t r;
    };

    struct ADD {
      uint64_t r;
    };

    struct SUB {
      uint64_t r;
    };

    struct IAC {};

    struct DAC {};

    struct CLC {};

    struct STC {};

    struct CMC {};

    struct CMA {};

    struct CLB {};

    struct RAL {};

    struct RAR {};

    struct TCC {};

    struct TCS {};

    struct DAA {};

    struct KBP {};

    struct JUN {
      uint64_t a;
    };

    struct JMS {
      uint64_t a;
    };

    struct JCN {
      uint64_t c;
      uint64_t a;
    };

    struct FIM {
      uint64_t r;
      uint64_t d;
    };

    struct SRC {
      uint64_t r;
    };

    struct FIN {
      uint64_t r;
    };

    struct JIN {
      uint64_t r;
    };

    struct ISZ {
      uint64_t r;
      uint64_t a;
    };

    struct BBL {
      uint64_t d;
    };

    using variant_t =
        std::variant<NOP, LDM, LD, XCH, INC, ADD, SUB, IAC, DAC, CLC, STC, CMC,
                     CMA, CLB, RAL, RAR, TCC, TCS, DAA, KBP, JUN, JMS, JCN, FIM,
                     SRC, FIN, JIN, ISZ, BBL>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    instr() {}

    explicit instr(NOP _v) : v_(_v) {}

    explicit instr(LDM _v) : v_(std::move(_v)) {}

    explicit instr(LD _v) : v_(std::move(_v)) {}

    explicit instr(XCH _v) : v_(std::move(_v)) {}

    explicit instr(INC _v) : v_(std::move(_v)) {}

    explicit instr(ADD _v) : v_(std::move(_v)) {}

    explicit instr(SUB _v) : v_(std::move(_v)) {}

    explicit instr(IAC _v) : v_(_v) {}

    explicit instr(DAC _v) : v_(_v) {}

    explicit instr(CLC _v) : v_(_v) {}

    explicit instr(STC _v) : v_(_v) {}

    explicit instr(CMC _v) : v_(_v) {}

    explicit instr(CMA _v) : v_(_v) {}

    explicit instr(CLB _v) : v_(_v) {}

    explicit instr(RAL _v) : v_(_v) {}

    explicit instr(RAR _v) : v_(_v) {}

    explicit instr(TCC _v) : v_(_v) {}

    explicit instr(TCS _v) : v_(_v) {}

    explicit instr(DAA _v) : v_(_v) {}

    explicit instr(KBP _v) : v_(_v) {}

    explicit instr(JUN _v) : v_(std::move(_v)) {}

    explicit instr(JMS _v) : v_(std::move(_v)) {}

    explicit instr(JCN _v) : v_(std::move(_v)) {}

    explicit instr(FIM _v) : v_(std::move(_v)) {}

    explicit instr(SRC _v) : v_(std::move(_v)) {}

    explicit instr(FIN _v) : v_(std::move(_v)) {}

    explicit instr(JIN _v) : v_(std::move(_v)) {}

    explicit instr(ISZ _v) : v_(std::move(_v)) {}

    explicit instr(BBL _v) : v_(std::move(_v)) {}

    static instr nop() { return instr(NOP{}); }

    static instr ldm(uint64_t n) { return instr(LDM{n}); }

    static instr ld(uint64_t r) { return instr(LD{r}); }

    static instr xch(uint64_t r) { return instr(XCH{r}); }

    static instr inc(uint64_t r) { return instr(INC{r}); }

    static instr add(uint64_t r) { return instr(ADD{r}); }

    static instr sub(uint64_t r) { return instr(SUB{r}); }

    static instr iac() { return instr(IAC{}); }

    static instr dac() { return instr(DAC{}); }

    static instr clc() { return instr(CLC{}); }

    static instr stc() { return instr(STC{}); }

    static instr cmc() { return instr(CMC{}); }

    static instr cma() { return instr(CMA{}); }

    static instr clb() { return instr(CLB{}); }

    static instr ral() { return instr(RAL{}); }

    static instr rar() { return instr(RAR{}); }

    static instr tcc() { return instr(TCC{}); }

    static instr tcs() { return instr(TCS{}); }

    static instr daa() { return instr(DAA{}); }

    static instr kbp() { return instr(KBP{}); }

    static instr jun(uint64_t a) { return instr(JUN{a}); }

    static instr jms(uint64_t a) { return instr(JMS{a}); }

    static instr jcn(uint64_t c, uint64_t a) { return instr(JCN{c, a}); }

    static instr fim(uint64_t r, uint64_t d) { return instr(FIM{r, d}); }

    static instr src(uint64_t r) { return instr(SRC{r}); }

    static instr fin(uint64_t r) { return instr(FIN{r}); }

    static instr jin(uint64_t r) { return instr(JIN{r}); }

    static instr isz(uint64_t r, uint64_t a) { return instr(ISZ{r, a}); }

    static instr bbl(uint64_t d) { return instr(BBL{d}); }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename F1, typename F2, typename F3, typename F4,
            typename F5, typename F6, typename F20, typename F21, typename F22,
            typename F23, typename F24, typename F25, typename F26,
            typename F27, typename F28>
    requires std::is_invocable_r_v<T1, F1 &, uint64_t &> &&
             std::is_invocable_r_v<T1, F2 &, uint64_t &> &&
             std::is_invocable_r_v<T1, F3 &, uint64_t &> &&
             std::is_invocable_r_v<T1, F4 &, uint64_t &> &&
             std::is_invocable_r_v<T1, F5 &, uint64_t &> &&
             std::is_invocable_r_v<T1, F6 &, uint64_t &> &&
             std::is_invocable_r_v<T1, F20 &, uint64_t &> &&
             std::is_invocable_r_v<T1, F21 &, uint64_t &> &&
             std::is_invocable_r_v<T1, F22 &, uint64_t &, uint64_t &> &&
             std::is_invocable_r_v<T1, F23 &, uint64_t &, uint64_t &> &&
             std::is_invocable_r_v<T1, F24 &, uint64_t &> &&
             std::is_invocable_r_v<T1, F25 &, uint64_t &> &&
             std::is_invocable_r_v<T1, F26 &, uint64_t &> &&
             std::is_invocable_r_v<T1, F27 &, uint64_t &, uint64_t &> &&
             std::is_invocable_r_v<T1, F28 &, uint64_t &>
  static T1 instr_rect(T1 f, F1 &&f0, F2 &&f1, F3 &&f2, F4 &&f3, F5 &&f4,
                       F6 &&f5, T1 f6, T1 f7, T1 f8, T1 f9, T1 f10, T1 f11,
                       T1 f12, T1 f13, T1 f14, T1 f15, T1 f16, T1 f17, T1 f18,
                       F20 &&f19, F21 &&f20, F22 &&f21, F23 &&f22, F24 &&f23,
                       F25 &&f24, F26 &&f25, F27 &&f26, F28 &&f27,
                       const instr &i) {
    if (std::holds_alternative<typename instr::NOP>(i.v())) {
      return f;
    } else if (std::holds_alternative<typename instr::LDM>(i.v())) {
      const auto &[n0] = std::get<typename instr::LDM>(i.v());
      return f0(n0);
    } else if (std::holds_alternative<typename instr::LD>(i.v())) {
      const auto &[r0] = std::get<typename instr::LD>(i.v());
      return f1(r0);
    } else if (std::holds_alternative<typename instr::XCH>(i.v())) {
      const auto &[r0] = std::get<typename instr::XCH>(i.v());
      return f2(r0);
    } else if (std::holds_alternative<typename instr::INC>(i.v())) {
      const auto &[r0] = std::get<typename instr::INC>(i.v());
      return f3(r0);
    } else if (std::holds_alternative<typename instr::ADD>(i.v())) {
      const auto &[r0] = std::get<typename instr::ADD>(i.v());
      return f4(r0);
    } else if (std::holds_alternative<typename instr::SUB>(i.v())) {
      const auto &[r0] = std::get<typename instr::SUB>(i.v());
      return f5(r0);
    } else if (std::holds_alternative<typename instr::IAC>(i.v())) {
      return f6;
    } else if (std::holds_alternative<typename instr::DAC>(i.v())) {
      return f7;
    } else if (std::holds_alternative<typename instr::CLC>(i.v())) {
      return f8;
    } else if (std::holds_alternative<typename instr::STC>(i.v())) {
      return f9;
    } else if (std::holds_alternative<typename instr::CMC>(i.v())) {
      return f10;
    } else if (std::holds_alternative<typename instr::CMA>(i.v())) {
      return f11;
    } else if (std::holds_alternative<typename instr::CLB>(i.v())) {
      return f12;
    } else if (std::holds_alternative<typename instr::RAL>(i.v())) {
      return f13;
    } else if (std::holds_alternative<typename instr::RAR>(i.v())) {
      return f14;
    } else if (std::holds_alternative<typename instr::TCC>(i.v())) {
      return f15;
    } else if (std::holds_alternative<typename instr::TCS>(i.v())) {
      return f16;
    } else if (std::holds_alternative<typename instr::DAA>(i.v())) {
      return f17;
    } else if (std::holds_alternative<typename instr::KBP>(i.v())) {
      return f18;
    } else if (std::holds_alternative<typename instr::JUN>(i.v())) {
      const auto &[a0] = std::get<typename instr::JUN>(i.v());
      return f19(a0);
    } else if (std::holds_alternative<typename instr::JMS>(i.v())) {
      const auto &[a0] = std::get<typename instr::JMS>(i.v());
      return f20(a0);
    } else if (std::holds_alternative<typename instr::JCN>(i.v())) {
      const auto &[c0, a0] = std::get<typename instr::JCN>(i.v());
      return f21(c0, a0);
    } else if (std::holds_alternative<typename instr::FIM>(i.v())) {
      const auto &[r0, d0] = std::get<typename instr::FIM>(i.v());
      return f22(r0, d0);
    } else if (std::holds_alternative<typename instr::SRC>(i.v())) {
      const auto &[r0] = std::get<typename instr::SRC>(i.v());
      return f23(r0);
    } else if (std::holds_alternative<typename instr::FIN>(i.v())) {
      const auto &[r0] = std::get<typename instr::FIN>(i.v());
      return f24(r0);
    } else if (std::holds_alternative<typename instr::JIN>(i.v())) {
      const auto &[r0] = std::get<typename instr::JIN>(i.v());
      return f25(r0);
    } else if (std::holds_alternative<typename instr::ISZ>(i.v())) {
      const auto &[r0, a0] = std::get<typename instr::ISZ>(i.v());
      return f26(r0, a0);
    } else {
      const auto &[d0] = std::get<typename instr::BBL>(i.v());
      return f27(d0);
    }
  }

  template <typename T1, typename F1, typename F2, typename F3, typename F4,
            typename F5, typename F6, typename F20, typename F21, typename F22,
            typename F23, typename F24, typename F25, typename F26,
            typename F27, typename F28>
    requires std::is_invocable_r_v<T1, F1 &, uint64_t &> &&
             std::is_invocable_r_v<T1, F2 &, uint64_t &> &&
             std::is_invocable_r_v<T1, F3 &, uint64_t &> &&
             std::is_invocable_r_v<T1, F4 &, uint64_t &> &&
             std::is_invocable_r_v<T1, F5 &, uint64_t &> &&
             std::is_invocable_r_v<T1, F6 &, uint64_t &> &&
             std::is_invocable_r_v<T1, F20 &, uint64_t &> &&
             std::is_invocable_r_v<T1, F21 &, uint64_t &> &&
             std::is_invocable_r_v<T1, F22 &, uint64_t &, uint64_t &> &&
             std::is_invocable_r_v<T1, F23 &, uint64_t &, uint64_t &> &&
             std::is_invocable_r_v<T1, F24 &, uint64_t &> &&
             std::is_invocable_r_v<T1, F25 &, uint64_t &> &&
             std::is_invocable_r_v<T1, F26 &, uint64_t &> &&
             std::is_invocable_r_v<T1, F27 &, uint64_t &, uint64_t &> &&
             std::is_invocable_r_v<T1, F28 &, uint64_t &>
  static T1 instr_rec(T1 f, F1 &&f0, F2 &&f1, F3 &&f2, F4 &&f3, F5 &&f4,
                      F6 &&f5, T1 f6, T1 f7, T1 f8, T1 f9, T1 f10, T1 f11,
                      T1 f12, T1 f13, T1 f14, T1 f15, T1 f16, T1 f17, T1 f18,
                      F20 &&f19, F21 &&f20, F22 &&f21, F23 &&f22, F24 &&f23,
                      F25 &&f24, F26 &&f25, F27 &&f26, F28 &&f27,
                      const instr &i) {
    if (std::holds_alternative<typename instr::NOP>(i.v())) {
      return f;
    } else if (std::holds_alternative<typename instr::LDM>(i.v())) {
      const auto &[n0] = std::get<typename instr::LDM>(i.v());
      return f0(n0);
    } else if (std::holds_alternative<typename instr::LD>(i.v())) {
      const auto &[r0] = std::get<typename instr::LD>(i.v());
      return f1(r0);
    } else if (std::holds_alternative<typename instr::XCH>(i.v())) {
      const auto &[r0] = std::get<typename instr::XCH>(i.v());
      return f2(r0);
    } else if (std::holds_alternative<typename instr::INC>(i.v())) {
      const auto &[r0] = std::get<typename instr::INC>(i.v());
      return f3(r0);
    } else if (std::holds_alternative<typename instr::ADD>(i.v())) {
      const auto &[r0] = std::get<typename instr::ADD>(i.v());
      return f4(r0);
    } else if (std::holds_alternative<typename instr::SUB>(i.v())) {
      const auto &[r0] = std::get<typename instr::SUB>(i.v());
      return f5(r0);
    } else if (std::holds_alternative<typename instr::IAC>(i.v())) {
      return f6;
    } else if (std::holds_alternative<typename instr::DAC>(i.v())) {
      return f7;
    } else if (std::holds_alternative<typename instr::CLC>(i.v())) {
      return f8;
    } else if (std::holds_alternative<typename instr::STC>(i.v())) {
      return f9;
    } else if (std::holds_alternative<typename instr::CMC>(i.v())) {
      return f10;
    } else if (std::holds_alternative<typename instr::CMA>(i.v())) {
      return f11;
    } else if (std::holds_alternative<typename instr::CLB>(i.v())) {
      return f12;
    } else if (std::holds_alternative<typename instr::RAL>(i.v())) {
      return f13;
    } else if (std::holds_alternative<typename instr::RAR>(i.v())) {
      return f14;
    } else if (std::holds_alternative<typename instr::TCC>(i.v())) {
      return f15;
    } else if (std::holds_alternative<typename instr::TCS>(i.v())) {
      return f16;
    } else if (std::holds_alternative<typename instr::DAA>(i.v())) {
      return f17;
    } else if (std::holds_alternative<typename instr::KBP>(i.v())) {
      return f18;
    } else if (std::holds_alternative<typename instr::JUN>(i.v())) {
      const auto &[a0] = std::get<typename instr::JUN>(i.v());
      return f19(a0);
    } else if (std::holds_alternative<typename instr::JMS>(i.v())) {
      const auto &[a0] = std::get<typename instr::JMS>(i.v());
      return f20(a0);
    } else if (std::holds_alternative<typename instr::JCN>(i.v())) {
      const auto &[c0, a0] = std::get<typename instr::JCN>(i.v());
      return f21(c0, a0);
    } else if (std::holds_alternative<typename instr::FIM>(i.v())) {
      const auto &[r0, d0] = std::get<typename instr::FIM>(i.v());
      return f22(r0, d0);
    } else if (std::holds_alternative<typename instr::SRC>(i.v())) {
      const auto &[r0] = std::get<typename instr::SRC>(i.v());
      return f23(r0);
    } else if (std::holds_alternative<typename instr::FIN>(i.v())) {
      const auto &[r0] = std::get<typename instr::FIN>(i.v());
      return f24(r0);
    } else if (std::holds_alternative<typename instr::JIN>(i.v())) {
      const auto &[r0] = std::get<typename instr::JIN>(i.v());
      return f25(r0);
    } else if (std::holds_alternative<typename instr::ISZ>(i.v())) {
      const auto &[r0, a0] = std::get<typename instr::ISZ>(i.v());
      return f26(r0, a0);
    } else {
      const auto &[d0] = std::get<typename instr::BBL>(i.v());
      return f27(d0);
    }
  }

  static state execute(const state &s, const instr &i);
  static inline const state sample = state{
      UINT64_C(3),
      List<uint64_t>::cons(
          UINT64_C(1),
          List<uint64_t>::cons(
              UINT64_C(2),
              List<uint64_t>::cons(
                  UINT64_C(3),
                  List<uint64_t>::cons(
                      UINT64_C(4),
                      List<uint64_t>::cons(
                          UINT64_C(5),
                          List<uint64_t>::cons(
                              UINT64_C(6),
                              List<uint64_t>::cons(
                                  UINT64_C(7),
                                  List<uint64_t>::cons(
                                      UINT64_C(8),
                                      List<uint64_t>::cons(
                                          UINT64_C(9),
                                          List<uint64_t>::cons(
                                              UINT64_C(10),
                                              List<uint64_t>::cons(
                                                  UINT64_C(11),
                                                  List<uint64_t>::cons(
                                                      UINT64_C(12),
                                                      List<uint64_t>::cons(
                                                          UINT64_C(13),
                                                          List<uint64_t>::cons(
                                                              UINT64_C(14),
                                                              List<uint64_t>::cons(
                                                                  UINT64_C(15),
                                                                  List<uint64_t>::cons(
                                                                      UINT64_C(
                                                                          0),
                                                                      List<
                                                                          uint64_t>::
                                                                          nil())))))))))))))))),
      false,
      UINT64_C(10),
      List<uint64_t>::cons(
          UINT64_C(20),
          List<uint64_t>::cons(UINT64_C(30), List<uint64_t>::nil())),
      UINT64_C(42),
      List<uint64_t>::cons(
          UINT64_C(1),
          List<uint64_t>::cons(
              UINT64_C(2),
              List<uint64_t>::cons(
                  UINT64_C(3),
                  List<uint64_t>::cons(UINT64_C(4), List<uint64_t>::nil()))))};
};

template <typename T1>
T1 ListDef::nth(uint64_t n, const List<T1> &l, T1 default0) {
  if (n <= 0) {
    if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
      return default0;
    } else {
      const auto &[a0, a1] = std::get<typename List<T1>::Cons>(l.v());
      return a0;
    }
  } else {
    uint64_t m = n - 1;
    if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
      return default0;
    } else {
      const auto &[a00, a10] = std::get<typename List<T1>::Cons>(l.v());
      return ListDef::template nth<T1>(m, *a10, default0);
    }
  }
}

#endif // INCLUDED_GET_PAIR_BOUND_PROP
