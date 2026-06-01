#ifndef INCLUDED_INSTRUCTION_CLASSIFIERS
#define INCLUDED_INSTRUCTION_CLASSIFIERS

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

struct InstructionClassifiers {
  struct instr_acc {
    // TYPES
    struct LDM {
      uint64_t a0;
    };

    struct LD {
      uint64_t a0;
    };

    struct ADD {
      uint64_t a0;
    };

    struct SUB {
      uint64_t a0;
    };

    struct INC {
      uint64_t a0;
    };

    struct XCH {
      uint64_t a0;
    };

    struct BBL {
      uint64_t a0;
    };

    struct SBM {};

    struct RDM {};

    struct RDR {};

    struct ADM {};

    struct RD0 {};

    struct RD1 {};

    struct RD2 {};

    struct RD3 {};

    struct CLB {};

    struct CMA {};

    struct IAC {};

    struct DAC {};

    struct RAL {};

    struct RAR {};

    struct TCC {};

    struct TCS {};

    struct DAA {};

    struct KBP {};

    struct NOP_acc {};

    using variant_t = std::variant<LDM, LD, ADD, SUB, INC, XCH, BBL, SBM, RDM,
                                   RDR, ADM, RD0, RD1, RD2, RD3, CLB, CMA, IAC,
                                   DAC, RAL, RAR, TCC, TCS, DAA, KBP, NOP_acc>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    instr_acc() {}

    explicit instr_acc(LDM _v) : v_(std::move(_v)) {}

    explicit instr_acc(LD _v) : v_(std::move(_v)) {}

    explicit instr_acc(ADD _v) : v_(std::move(_v)) {}

    explicit instr_acc(SUB _v) : v_(std::move(_v)) {}

    explicit instr_acc(INC _v) : v_(std::move(_v)) {}

    explicit instr_acc(XCH _v) : v_(std::move(_v)) {}

    explicit instr_acc(BBL _v) : v_(std::move(_v)) {}

    explicit instr_acc(SBM _v) : v_(_v) {}

    explicit instr_acc(RDM _v) : v_(_v) {}

    explicit instr_acc(RDR _v) : v_(_v) {}

    explicit instr_acc(ADM _v) : v_(_v) {}

    explicit instr_acc(RD0 _v) : v_(_v) {}

    explicit instr_acc(RD1 _v) : v_(_v) {}

    explicit instr_acc(RD2 _v) : v_(_v) {}

    explicit instr_acc(RD3 _v) : v_(_v) {}

    explicit instr_acc(CLB _v) : v_(_v) {}

    explicit instr_acc(CMA _v) : v_(_v) {}

    explicit instr_acc(IAC _v) : v_(_v) {}

    explicit instr_acc(DAC _v) : v_(_v) {}

    explicit instr_acc(RAL _v) : v_(_v) {}

    explicit instr_acc(RAR _v) : v_(_v) {}

    explicit instr_acc(TCC _v) : v_(_v) {}

    explicit instr_acc(TCS _v) : v_(_v) {}

    explicit instr_acc(DAA _v) : v_(_v) {}

    explicit instr_acc(KBP _v) : v_(_v) {}

    explicit instr_acc(NOP_acc _v) : v_(_v) {}

    static instr_acc ldm(uint64_t a0) { return instr_acc(LDM{a0}); }

    static instr_acc ld(uint64_t a0) { return instr_acc(LD{a0}); }

    static instr_acc add(uint64_t a0) { return instr_acc(ADD{a0}); }

    static instr_acc sub(uint64_t a0) { return instr_acc(SUB{a0}); }

    static instr_acc inc(uint64_t a0) { return instr_acc(INC{a0}); }

    static instr_acc xch(uint64_t a0) { return instr_acc(XCH{a0}); }

    static instr_acc bbl(uint64_t a0) { return instr_acc(BBL{a0}); }

    static instr_acc sbm() { return instr_acc(SBM{}); }

    static instr_acc rdm() { return instr_acc(RDM{}); }

    static instr_acc rdr() { return instr_acc(RDR{}); }

    static instr_acc adm() { return instr_acc(ADM{}); }

    static instr_acc rd0() { return instr_acc(RD0{}); }

    static instr_acc rd1() { return instr_acc(RD1{}); }

    static instr_acc rd2() { return instr_acc(RD2{}); }

    static instr_acc rd3() { return instr_acc(RD3{}); }

    static instr_acc clb() { return instr_acc(CLB{}); }

    static instr_acc cma() { return instr_acc(CMA{}); }

    static instr_acc iac() { return instr_acc(IAC{}); }

    static instr_acc dac() { return instr_acc(DAC{}); }

    static instr_acc ral() { return instr_acc(RAL{}); }

    static instr_acc rar() { return instr_acc(RAR{}); }

    static instr_acc tcc() { return instr_acc(TCC{}); }

    static instr_acc tcs() { return instr_acc(TCS{}); }

    static instr_acc daa() { return instr_acc(DAA{}); }

    static instr_acc kbp() { return instr_acc(KBP{}); }

    static instr_acc nop_acc() { return instr_acc(NOP_acc{}); }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    bool writes_acc() const {
      if (std::holds_alternative<typename instr_acc::NOP_acc>(this->v())) {
        return false;
      } else {
        return true;
      }
    }

    template <typename T1, typename F0, typename F1, typename F2, typename F3,
              typename F4, typename F5, typename F6>
      requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
               std::is_invocable_r_v<T1, F1 &, uint64_t &> &&
               std::is_invocable_r_v<T1, F2 &, uint64_t &> &&
               std::is_invocable_r_v<T1, F3 &, uint64_t &> &&
               std::is_invocable_r_v<T1, F4 &, uint64_t &> &&
               std::is_invocable_r_v<T1, F5 &, uint64_t &> &&
               std::is_invocable_r_v<T1, F6 &, uint64_t &>
    T1 instr_acc_rec(F0 &&f, F1 &&f0, F2 &&f1, F3 &&f2, F4 &&f3, F5 &&f4,
                     F6 &&f5, T1 f6, T1 f7, T1 f8, T1 f9, T1 f10, T1 f11,
                     T1 f12, T1 f13, T1 f14, T1 f15, T1 f16, T1 f17, T1 f18,
                     T1 f19, T1 f20, T1 f21, T1 f22, T1 f23, T1 f24) const {
      if (std::holds_alternative<typename instr_acc::LDM>(this->v())) {
        const auto &[a0] = std::get<typename instr_acc::LDM>(this->v());
        return f(a0);
      } else if (std::holds_alternative<typename instr_acc::LD>(this->v())) {
        const auto &[a0] = std::get<typename instr_acc::LD>(this->v());
        return f0(a0);
      } else if (std::holds_alternative<typename instr_acc::ADD>(this->v())) {
        const auto &[a0] = std::get<typename instr_acc::ADD>(this->v());
        return f1(a0);
      } else if (std::holds_alternative<typename instr_acc::SUB>(this->v())) {
        const auto &[a0] = std::get<typename instr_acc::SUB>(this->v());
        return f2(a0);
      } else if (std::holds_alternative<typename instr_acc::INC>(this->v())) {
        const auto &[a0] = std::get<typename instr_acc::INC>(this->v());
        return f3(a0);
      } else if (std::holds_alternative<typename instr_acc::XCH>(this->v())) {
        const auto &[a0] = std::get<typename instr_acc::XCH>(this->v());
        return f4(a0);
      } else if (std::holds_alternative<typename instr_acc::BBL>(this->v())) {
        const auto &[a0] = std::get<typename instr_acc::BBL>(this->v());
        return f5(a0);
      } else if (std::holds_alternative<typename instr_acc::SBM>(this->v())) {
        return f6;
      } else if (std::holds_alternative<typename instr_acc::RDM>(this->v())) {
        return f7;
      } else if (std::holds_alternative<typename instr_acc::RDR>(this->v())) {
        return f8;
      } else if (std::holds_alternative<typename instr_acc::ADM>(this->v())) {
        return f9;
      } else if (std::holds_alternative<typename instr_acc::RD0>(this->v())) {
        return f10;
      } else if (std::holds_alternative<typename instr_acc::RD1>(this->v())) {
        return f11;
      } else if (std::holds_alternative<typename instr_acc::RD2>(this->v())) {
        return f12;
      } else if (std::holds_alternative<typename instr_acc::RD3>(this->v())) {
        return f13;
      } else if (std::holds_alternative<typename instr_acc::CLB>(this->v())) {
        return f14;
      } else if (std::holds_alternative<typename instr_acc::CMA>(this->v())) {
        return f15;
      } else if (std::holds_alternative<typename instr_acc::IAC>(this->v())) {
        return f16;
      } else if (std::holds_alternative<typename instr_acc::DAC>(this->v())) {
        return f17;
      } else if (std::holds_alternative<typename instr_acc::RAL>(this->v())) {
        return f18;
      } else if (std::holds_alternative<typename instr_acc::RAR>(this->v())) {
        return f19;
      } else if (std::holds_alternative<typename instr_acc::TCC>(this->v())) {
        return f20;
      } else if (std::holds_alternative<typename instr_acc::TCS>(this->v())) {
        return f21;
      } else if (std::holds_alternative<typename instr_acc::DAA>(this->v())) {
        return f22;
      } else if (std::holds_alternative<typename instr_acc::KBP>(this->v())) {
        return f23;
      } else {
        return f24;
      }
    }

    template <typename T1, typename F0, typename F1, typename F2, typename F3,
              typename F4, typename F5, typename F6>
      requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
               std::is_invocable_r_v<T1, F1 &, uint64_t &> &&
               std::is_invocable_r_v<T1, F2 &, uint64_t &> &&
               std::is_invocable_r_v<T1, F3 &, uint64_t &> &&
               std::is_invocable_r_v<T1, F4 &, uint64_t &> &&
               std::is_invocable_r_v<T1, F5 &, uint64_t &> &&
               std::is_invocable_r_v<T1, F6 &, uint64_t &>
    T1 instr_acc_rect(F0 &&f, F1 &&f0, F2 &&f1, F3 &&f2, F4 &&f3, F5 &&f4,
                      F6 &&f5, T1 f6, T1 f7, T1 f8, T1 f9, T1 f10, T1 f11,
                      T1 f12, T1 f13, T1 f14, T1 f15, T1 f16, T1 f17, T1 f18,
                      T1 f19, T1 f20, T1 f21, T1 f22, T1 f23, T1 f24) const {
      if (std::holds_alternative<typename instr_acc::LDM>(this->v())) {
        const auto &[a0] = std::get<typename instr_acc::LDM>(this->v());
        return f(a0);
      } else if (std::holds_alternative<typename instr_acc::LD>(this->v())) {
        const auto &[a0] = std::get<typename instr_acc::LD>(this->v());
        return f0(a0);
      } else if (std::holds_alternative<typename instr_acc::ADD>(this->v())) {
        const auto &[a0] = std::get<typename instr_acc::ADD>(this->v());
        return f1(a0);
      } else if (std::holds_alternative<typename instr_acc::SUB>(this->v())) {
        const auto &[a0] = std::get<typename instr_acc::SUB>(this->v());
        return f2(a0);
      } else if (std::holds_alternative<typename instr_acc::INC>(this->v())) {
        const auto &[a0] = std::get<typename instr_acc::INC>(this->v());
        return f3(a0);
      } else if (std::holds_alternative<typename instr_acc::XCH>(this->v())) {
        const auto &[a0] = std::get<typename instr_acc::XCH>(this->v());
        return f4(a0);
      } else if (std::holds_alternative<typename instr_acc::BBL>(this->v())) {
        const auto &[a0] = std::get<typename instr_acc::BBL>(this->v());
        return f5(a0);
      } else if (std::holds_alternative<typename instr_acc::SBM>(this->v())) {
        return f6;
      } else if (std::holds_alternative<typename instr_acc::RDM>(this->v())) {
        return f7;
      } else if (std::holds_alternative<typename instr_acc::RDR>(this->v())) {
        return f8;
      } else if (std::holds_alternative<typename instr_acc::ADM>(this->v())) {
        return f9;
      } else if (std::holds_alternative<typename instr_acc::RD0>(this->v())) {
        return f10;
      } else if (std::holds_alternative<typename instr_acc::RD1>(this->v())) {
        return f11;
      } else if (std::holds_alternative<typename instr_acc::RD2>(this->v())) {
        return f12;
      } else if (std::holds_alternative<typename instr_acc::RD3>(this->v())) {
        return f13;
      } else if (std::holds_alternative<typename instr_acc::CLB>(this->v())) {
        return f14;
      } else if (std::holds_alternative<typename instr_acc::CMA>(this->v())) {
        return f15;
      } else if (std::holds_alternative<typename instr_acc::IAC>(this->v())) {
        return f16;
      } else if (std::holds_alternative<typename instr_acc::DAC>(this->v())) {
        return f17;
      } else if (std::holds_alternative<typename instr_acc::RAL>(this->v())) {
        return f18;
      } else if (std::holds_alternative<typename instr_acc::RAR>(this->v())) {
        return f19;
      } else if (std::holds_alternative<typename instr_acc::TCC>(this->v())) {
        return f20;
      } else if (std::holds_alternative<typename instr_acc::TCS>(this->v())) {
        return f21;
      } else if (std::holds_alternative<typename instr_acc::DAA>(this->v())) {
        return f22;
      } else if (std::holds_alternative<typename instr_acc::KBP>(this->v())) {
        return f23;
      } else {
        return f24;
      }
    }
  };

  static uint64_t count_writes_acc(const List<instr_acc> &prog);
  static inline const uint64_t test_writes_acc =
      count_writes_acc(List<instr_acc>::cons(
          instr_acc::nop_acc(),
          List<instr_acc>::cons(
              instr_acc::ldm(UINT64_C(9)),
              List<instr_acc>::cons(
                  instr_acc::rar(),
                  List<instr_acc>::cons(
                      instr_acc::kbp(),
                      List<instr_acc>::cons(
                          instr_acc::nop_acc(),
                          List<instr_acc>::cons(instr_acc::add(UINT64_C(1)),
                                                List<instr_acc>::nil())))))));

  struct instr_ram {
    // TYPES
    struct WRM {};

    struct WMP {};

    struct WR0 {};

    struct WR1 {};

    struct WR2 {};

    struct WR3 {};

    struct NOP_ram {};

    struct ADD_ram {
      uint64_t a0;
    };

    using variant_t =
        std::variant<WRM, WMP, WR0, WR1, WR2, WR3, NOP_ram, ADD_ram>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    instr_ram() {}

    explicit instr_ram(WRM _v) : v_(_v) {}

    explicit instr_ram(WMP _v) : v_(_v) {}

    explicit instr_ram(WR0 _v) : v_(_v) {}

    explicit instr_ram(WR1 _v) : v_(_v) {}

    explicit instr_ram(WR2 _v) : v_(_v) {}

    explicit instr_ram(WR3 _v) : v_(_v) {}

    explicit instr_ram(NOP_ram _v) : v_(_v) {}

    explicit instr_ram(ADD_ram _v) : v_(std::move(_v)) {}

    static instr_ram wrm() { return instr_ram(WRM{}); }

    static instr_ram wmp() { return instr_ram(WMP{}); }

    static instr_ram wr0() { return instr_ram(WR0{}); }

    static instr_ram wr1() { return instr_ram(WR1{}); }

    static instr_ram wr2() { return instr_ram(WR2{}); }

    static instr_ram wr3() { return instr_ram(WR3{}); }

    static instr_ram nop_ram() { return instr_ram(NOP_ram{}); }

    static instr_ram add_ram(uint64_t a0) { return instr_ram(ADD_ram{a0}); }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    bool writes_ram() const {
      if (std::holds_alternative<typename instr_ram::NOP_ram>(this->v())) {
        return false;
      } else if (std::holds_alternative<typename instr_ram::ADD_ram>(
                     this->v())) {
        return false;
      } else {
        return true;
      }
    }

    template <typename T1, typename F7>
      requires std::is_invocable_r_v<T1, F7 &, uint64_t &>
    T1 instr_ram_rec(T1 f, T1 f0, T1 f1, T1 f2, T1 f3, T1 f4, T1 f5,
                     F7 &&f6) const {
      if (std::holds_alternative<typename instr_ram::WRM>(this->v())) {
        return f;
      } else if (std::holds_alternative<typename instr_ram::WMP>(this->v())) {
        return f0;
      } else if (std::holds_alternative<typename instr_ram::WR0>(this->v())) {
        return f1;
      } else if (std::holds_alternative<typename instr_ram::WR1>(this->v())) {
        return f2;
      } else if (std::holds_alternative<typename instr_ram::WR2>(this->v())) {
        return f3;
      } else if (std::holds_alternative<typename instr_ram::WR3>(this->v())) {
        return f4;
      } else if (std::holds_alternative<typename instr_ram::NOP_ram>(
                     this->v())) {
        return f5;
      } else {
        const auto &[a0] = std::get<typename instr_ram::ADD_ram>(this->v());
        return f6(a0);
      }
    }

    template <typename T1, typename F7>
      requires std::is_invocable_r_v<T1, F7 &, uint64_t &>
    T1 instr_ram_rect(T1 f, T1 f0, T1 f1, T1 f2, T1 f3, T1 f4, T1 f5,
                      F7 &&f6) const {
      if (std::holds_alternative<typename instr_ram::WRM>(this->v())) {
        return f;
      } else if (std::holds_alternative<typename instr_ram::WMP>(this->v())) {
        return f0;
      } else if (std::holds_alternative<typename instr_ram::WR0>(this->v())) {
        return f1;
      } else if (std::holds_alternative<typename instr_ram::WR1>(this->v())) {
        return f2;
      } else if (std::holds_alternative<typename instr_ram::WR2>(this->v())) {
        return f3;
      } else if (std::holds_alternative<typename instr_ram::WR3>(this->v())) {
        return f4;
      } else if (std::holds_alternative<typename instr_ram::NOP_ram>(
                     this->v())) {
        return f5;
      } else {
        const auto &[a0] = std::get<typename instr_ram::ADD_ram>(this->v());
        return f6(a0);
      }
    }
  };

  static uint64_t count_writes_ram(const List<instr_ram> &prog);
  static inline const uint64_t test_writes_ram =
      count_writes_ram(List<instr_ram>::cons(
          instr_ram::nop_ram(),
          List<instr_ram>::cons(
              instr_ram::wrm(),
              List<instr_ram>::cons(
                  instr_ram::add_ram(UINT64_C(3)),
                  List<instr_ram>::cons(
                      instr_ram::wr3(),
                      List<instr_ram>::cons(
                          instr_ram::wmp(),
                          List<instr_ram>::cons(instr_ram::nop_ram(),
                                                List<instr_ram>::nil())))))));

  struct instr_regs {
    // TYPES
    struct XCH_regs {
      uint64_t a0;
    };

    struct INC_regs {
      uint64_t a0;
    };

    struct FIM {
      uint64_t a0;
      uint64_t a1;
    };

    struct FIN {
      uint64_t a0;
    };

    struct ISZ {
      uint64_t a0;
      uint64_t a1;
    };

    struct NOP_regs {};

    struct ADD_regs {
      uint64_t a0;
    };

    using variant_t =
        std::variant<XCH_regs, INC_regs, FIM, FIN, ISZ, NOP_regs, ADD_regs>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    instr_regs() {}

    explicit instr_regs(XCH_regs _v) : v_(std::move(_v)) {}

    explicit instr_regs(INC_regs _v) : v_(std::move(_v)) {}

    explicit instr_regs(FIM _v) : v_(std::move(_v)) {}

    explicit instr_regs(FIN _v) : v_(std::move(_v)) {}

    explicit instr_regs(ISZ _v) : v_(std::move(_v)) {}

    explicit instr_regs(NOP_regs _v) : v_(_v) {}

    explicit instr_regs(ADD_regs _v) : v_(std::move(_v)) {}

    static instr_regs xch_regs(uint64_t a0) { return instr_regs(XCH_regs{a0}); }

    static instr_regs inc_regs(uint64_t a0) { return instr_regs(INC_regs{a0}); }

    static instr_regs fim(uint64_t a0, uint64_t a1) {
      return instr_regs(FIM{a0, a1});
    }

    static instr_regs fin(uint64_t a0) { return instr_regs(FIN{a0}); }

    static instr_regs isz(uint64_t a0, uint64_t a1) {
      return instr_regs(ISZ{a0, a1});
    }

    static instr_regs nop_regs() { return instr_regs(NOP_regs{}); }

    static instr_regs add_regs(uint64_t a0) { return instr_regs(ADD_regs{a0}); }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    bool writes_regs() const {
      if (std::holds_alternative<typename instr_regs::NOP_regs>(this->v())) {
        return false;
      } else if (std::holds_alternative<typename instr_regs::ADD_regs>(
                     this->v())) {
        return false;
      } else {
        return true;
      }
    }

    template <typename T1, typename F0, typename F1, typename F2, typename F3,
              typename F4, typename F6>
      requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
               std::is_invocable_r_v<T1, F1 &, uint64_t &> &&
               std::is_invocable_r_v<T1, F2 &, uint64_t &, uint64_t &> &&
               std::is_invocable_r_v<T1, F3 &, uint64_t &> &&
               std::is_invocable_r_v<T1, F4 &, uint64_t &, uint64_t &> &&
               std::is_invocable_r_v<T1, F6 &, uint64_t &>
    T1 instr_regs_rec(F0 &&f, F1 &&f0, F2 &&f1, F3 &&f2, F4 &&f3, T1 f4,
                      F6 &&f5) const {
      if (std::holds_alternative<typename instr_regs::XCH_regs>(this->v())) {
        const auto &[a0] = std::get<typename instr_regs::XCH_regs>(this->v());
        return f(a0);
      } else if (std::holds_alternative<typename instr_regs::INC_regs>(
                     this->v())) {
        const auto &[a0] = std::get<typename instr_regs::INC_regs>(this->v());
        return f0(a0);
      } else if (std::holds_alternative<typename instr_regs::FIM>(this->v())) {
        const auto &[a0, a1] = std::get<typename instr_regs::FIM>(this->v());
        return f1(a0, a1);
      } else if (std::holds_alternative<typename instr_regs::FIN>(this->v())) {
        const auto &[a0] = std::get<typename instr_regs::FIN>(this->v());
        return f2(a0);
      } else if (std::holds_alternative<typename instr_regs::ISZ>(this->v())) {
        const auto &[a0, a1] = std::get<typename instr_regs::ISZ>(this->v());
        return f3(a0, a1);
      } else if (std::holds_alternative<typename instr_regs::NOP_regs>(
                     this->v())) {
        return f4;
      } else {
        const auto &[a0] = std::get<typename instr_regs::ADD_regs>(this->v());
        return f5(a0);
      }
    }

    template <typename T1, typename F0, typename F1, typename F2, typename F3,
              typename F4, typename F6>
      requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
               std::is_invocable_r_v<T1, F1 &, uint64_t &> &&
               std::is_invocable_r_v<T1, F2 &, uint64_t &, uint64_t &> &&
               std::is_invocable_r_v<T1, F3 &, uint64_t &> &&
               std::is_invocable_r_v<T1, F4 &, uint64_t &, uint64_t &> &&
               std::is_invocable_r_v<T1, F6 &, uint64_t &>
    T1 instr_regs_rect(F0 &&f, F1 &&f0, F2 &&f1, F3 &&f2, F4 &&f3, T1 f4,
                       F6 &&f5) const {
      if (std::holds_alternative<typename instr_regs::XCH_regs>(this->v())) {
        const auto &[a0] = std::get<typename instr_regs::XCH_regs>(this->v());
        return f(a0);
      } else if (std::holds_alternative<typename instr_regs::INC_regs>(
                     this->v())) {
        const auto &[a0] = std::get<typename instr_regs::INC_regs>(this->v());
        return f0(a0);
      } else if (std::holds_alternative<typename instr_regs::FIM>(this->v())) {
        const auto &[a0, a1] = std::get<typename instr_regs::FIM>(this->v());
        return f1(a0, a1);
      } else if (std::holds_alternative<typename instr_regs::FIN>(this->v())) {
        const auto &[a0] = std::get<typename instr_regs::FIN>(this->v());
        return f2(a0);
      } else if (std::holds_alternative<typename instr_regs::ISZ>(this->v())) {
        const auto &[a0, a1] = std::get<typename instr_regs::ISZ>(this->v());
        return f3(a0, a1);
      } else if (std::holds_alternative<typename instr_regs::NOP_regs>(
                     this->v())) {
        return f4;
      } else {
        const auto &[a0] = std::get<typename instr_regs::ADD_regs>(this->v());
        return f5(a0);
      }
    }
  };

  static uint64_t count_writes_regs(const List<instr_regs> &prog);
  static inline const uint64_t test_writes_regs =
      count_writes_regs(List<instr_regs>::cons(
          instr_regs::nop_regs(),
          List<instr_regs>::cons(
              instr_regs::fim(UINT64_C(0), UINT64_C(12)),
              List<instr_regs>::cons(
                  instr_regs::add_regs(UINT64_C(1)),
                  List<instr_regs>::cons(
                      instr_regs::inc_regs(UINT64_C(7)),
                      List<instr_regs>::cons(
                          instr_regs::isz(UINT64_C(1), UINT64_C(2)),
                          List<instr_regs>::nil()))))));

  struct instr_jump {
    // TYPES
    struct JCN {
      uint64_t a0;
      uint64_t a1;
    };

    struct JUN {
      uint64_t a0;
    };

    struct JMS {
      uint64_t a0;
    };

    struct JIN {
      uint64_t a0;
    };

    struct BBL_jump {
      uint64_t a0;
    };

    struct ISZ_jump {
      uint64_t a0;
      uint64_t a1;
    };

    struct ADD_jump {
      uint64_t a0;
    };

    struct NOP_jump {};

    using variant_t = std::variant<JCN, JUN, JMS, JIN, BBL_jump, ISZ_jump,
                                   ADD_jump, NOP_jump>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    instr_jump() {}

    explicit instr_jump(JCN _v) : v_(std::move(_v)) {}

    explicit instr_jump(JUN _v) : v_(std::move(_v)) {}

    explicit instr_jump(JMS _v) : v_(std::move(_v)) {}

    explicit instr_jump(JIN _v) : v_(std::move(_v)) {}

    explicit instr_jump(BBL_jump _v) : v_(std::move(_v)) {}

    explicit instr_jump(ISZ_jump _v) : v_(std::move(_v)) {}

    explicit instr_jump(ADD_jump _v) : v_(std::move(_v)) {}

    explicit instr_jump(NOP_jump _v) : v_(_v) {}

    static instr_jump jcn(uint64_t a0, uint64_t a1) {
      return instr_jump(JCN{a0, a1});
    }

    static instr_jump jun(uint64_t a0) { return instr_jump(JUN{a0}); }

    static instr_jump jms(uint64_t a0) { return instr_jump(JMS{a0}); }

    static instr_jump jin(uint64_t a0) { return instr_jump(JIN{a0}); }

    static instr_jump bbl_jump(uint64_t a0) { return instr_jump(BBL_jump{a0}); }

    static instr_jump isz_jump(uint64_t a0, uint64_t a1) {
      return instr_jump(ISZ_jump{a0, a1});
    }

    static instr_jump add_jump(uint64_t a0) { return instr_jump(ADD_jump{a0}); }

    static instr_jump nop_jump() { return instr_jump(NOP_jump{}); }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    bool is_jump() const {
      if (std::holds_alternative<typename instr_jump::ADD_jump>(this->v())) {
        return false;
      } else if (std::holds_alternative<typename instr_jump::NOP_jump>(
                     this->v())) {
        return false;
      } else {
        return true;
      }
    }

    template <typename T1, typename F0, typename F1, typename F2, typename F3,
              typename F4, typename F5, typename F6>
      requires std::is_invocable_r_v<T1, F0 &, uint64_t &, uint64_t &> &&
               std::is_invocable_r_v<T1, F1 &, uint64_t &> &&
               std::is_invocable_r_v<T1, F2 &, uint64_t &> &&
               std::is_invocable_r_v<T1, F3 &, uint64_t &> &&
               std::is_invocable_r_v<T1, F4 &, uint64_t &> &&
               std::is_invocable_r_v<T1, F5 &, uint64_t &, uint64_t &> &&
               std::is_invocable_r_v<T1, F6 &, uint64_t &>
    T1 instr_jump_rec(F0 &&f, F1 &&f0, F2 &&f1, F3 &&f2, F4 &&f3, F5 &&f4,
                      F6 &&f5, T1 f6) const {
      if (std::holds_alternative<typename instr_jump::JCN>(this->v())) {
        const auto &[a0, a1] = std::get<typename instr_jump::JCN>(this->v());
        return f(a0, a1);
      } else if (std::holds_alternative<typename instr_jump::JUN>(this->v())) {
        const auto &[a0] = std::get<typename instr_jump::JUN>(this->v());
        return f0(a0);
      } else if (std::holds_alternative<typename instr_jump::JMS>(this->v())) {
        const auto &[a0] = std::get<typename instr_jump::JMS>(this->v());
        return f1(a0);
      } else if (std::holds_alternative<typename instr_jump::JIN>(this->v())) {
        const auto &[a0] = std::get<typename instr_jump::JIN>(this->v());
        return f2(a0);
      } else if (std::holds_alternative<typename instr_jump::BBL_jump>(
                     this->v())) {
        const auto &[a0] = std::get<typename instr_jump::BBL_jump>(this->v());
        return f3(a0);
      } else if (std::holds_alternative<typename instr_jump::ISZ_jump>(
                     this->v())) {
        const auto &[a0, a1] =
            std::get<typename instr_jump::ISZ_jump>(this->v());
        return f4(a0, a1);
      } else if (std::holds_alternative<typename instr_jump::ADD_jump>(
                     this->v())) {
        const auto &[a0] = std::get<typename instr_jump::ADD_jump>(this->v());
        return f5(a0);
      } else {
        return f6;
      }
    }

    template <typename T1, typename F0, typename F1, typename F2, typename F3,
              typename F4, typename F5, typename F6>
      requires std::is_invocable_r_v<T1, F0 &, uint64_t &, uint64_t &> &&
               std::is_invocable_r_v<T1, F1 &, uint64_t &> &&
               std::is_invocable_r_v<T1, F2 &, uint64_t &> &&
               std::is_invocable_r_v<T1, F3 &, uint64_t &> &&
               std::is_invocable_r_v<T1, F4 &, uint64_t &> &&
               std::is_invocable_r_v<T1, F5 &, uint64_t &, uint64_t &> &&
               std::is_invocable_r_v<T1, F6 &, uint64_t &>
    T1 instr_jump_rect(F0 &&f, F1 &&f0, F2 &&f1, F3 &&f2, F4 &&f3, F5 &&f4,
                       F6 &&f5, T1 f6) const {
      if (std::holds_alternative<typename instr_jump::JCN>(this->v())) {
        const auto &[a0, a1] = std::get<typename instr_jump::JCN>(this->v());
        return f(a0, a1);
      } else if (std::holds_alternative<typename instr_jump::JUN>(this->v())) {
        const auto &[a0] = std::get<typename instr_jump::JUN>(this->v());
        return f0(a0);
      } else if (std::holds_alternative<typename instr_jump::JMS>(this->v())) {
        const auto &[a0] = std::get<typename instr_jump::JMS>(this->v());
        return f1(a0);
      } else if (std::holds_alternative<typename instr_jump::JIN>(this->v())) {
        const auto &[a0] = std::get<typename instr_jump::JIN>(this->v());
        return f2(a0);
      } else if (std::holds_alternative<typename instr_jump::BBL_jump>(
                     this->v())) {
        const auto &[a0] = std::get<typename instr_jump::BBL_jump>(this->v());
        return f3(a0);
      } else if (std::holds_alternative<typename instr_jump::ISZ_jump>(
                     this->v())) {
        const auto &[a0, a1] =
            std::get<typename instr_jump::ISZ_jump>(this->v());
        return f4(a0, a1);
      } else if (std::holds_alternative<typename instr_jump::ADD_jump>(
                     this->v())) {
        const auto &[a0] = std::get<typename instr_jump::ADD_jump>(this->v());
        return f5(a0);
      } else {
        return f6;
      }
    }
  };

  static uint64_t count_jumps(const List<instr_jump> &prog);
  static inline const uint64_t test_jump_classifier =
      count_jumps(List<instr_jump>::cons(
          instr_jump::add_jump(UINT64_C(0)),
          List<instr_jump>::cons(
              instr_jump::jcn(UINT64_C(4), UINT64_C(8)),
              List<instr_jump>::cons(
                  instr_jump::nop_jump(),
                  List<instr_jump>::cons(
                      instr_jump::jms(UINT64_C(33)),
                      List<instr_jump>::cons(
                          instr_jump::isz_jump(UINT64_C(1), UINT64_C(2)),
                          List<instr_jump>::nil()))))));

  static inline const std::pair<
      std::pair<std::pair<uint64_t, uint64_t>, uint64_t>, uint64_t>
      t = std::make_pair(
          std::make_pair(std::make_pair(test_writes_acc, test_writes_ram),
                         test_writes_regs),
          test_jump_classifier);
};

#endif // INCLUDED_INSTRUCTION_CLASSIFIERS
