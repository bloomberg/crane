#ifndef INCLUDED_INSTRUCTION_CLASSIFIERS
#define INCLUDED_INSTRUCTION_CLASSIFIERS

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

struct InstructionClassifiers {
  struct instr_acc {
    // TYPES
    struct LDM {
      unsigned int d_a0;
    };

    struct LD {
      unsigned int d_a0;
    };

    struct ADD {
      unsigned int d_a0;
    };

    struct SUB {
      unsigned int d_a0;
    };

    struct INC {
      unsigned int d_a0;
    };

    struct XCH {
      unsigned int d_a0;
    };

    struct BBL {
      unsigned int d_a0;
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
    variant_t d_v_;

  public:
    // CREATORS
    explicit instr_acc(LDM _v) : d_v_(std::move(_v)) {}

    explicit instr_acc(LD _v) : d_v_(std::move(_v)) {}

    explicit instr_acc(ADD _v) : d_v_(std::move(_v)) {}

    explicit instr_acc(SUB _v) : d_v_(std::move(_v)) {}

    explicit instr_acc(INC _v) : d_v_(std::move(_v)) {}

    explicit instr_acc(XCH _v) : d_v_(std::move(_v)) {}

    explicit instr_acc(BBL _v) : d_v_(std::move(_v)) {}

    explicit instr_acc(SBM _v) : d_v_(std::move(_v)) {}

    explicit instr_acc(RDM _v) : d_v_(std::move(_v)) {}

    explicit instr_acc(RDR _v) : d_v_(std::move(_v)) {}

    explicit instr_acc(ADM _v) : d_v_(std::move(_v)) {}

    explicit instr_acc(RD0 _v) : d_v_(std::move(_v)) {}

    explicit instr_acc(RD1 _v) : d_v_(std::move(_v)) {}

    explicit instr_acc(RD2 _v) : d_v_(std::move(_v)) {}

    explicit instr_acc(RD3 _v) : d_v_(std::move(_v)) {}

    explicit instr_acc(CLB _v) : d_v_(std::move(_v)) {}

    explicit instr_acc(CMA _v) : d_v_(std::move(_v)) {}

    explicit instr_acc(IAC _v) : d_v_(std::move(_v)) {}

    explicit instr_acc(DAC _v) : d_v_(std::move(_v)) {}

    explicit instr_acc(RAL _v) : d_v_(std::move(_v)) {}

    explicit instr_acc(RAR _v) : d_v_(std::move(_v)) {}

    explicit instr_acc(TCC _v) : d_v_(std::move(_v)) {}

    explicit instr_acc(TCS _v) : d_v_(std::move(_v)) {}

    explicit instr_acc(DAA _v) : d_v_(std::move(_v)) {}

    explicit instr_acc(KBP _v) : d_v_(std::move(_v)) {}

    explicit instr_acc(NOP_acc _v) : d_v_(std::move(_v)) {}

    static std::shared_ptr<instr_acc> ldm(unsigned int a0) {
      return std::make_shared<instr_acc>(LDM{std::move(a0)});
    }

    static std::shared_ptr<instr_acc> ld(unsigned int a0) {
      return std::make_shared<instr_acc>(LD{std::move(a0)});
    }

    static std::shared_ptr<instr_acc> add(unsigned int a0) {
      return std::make_shared<instr_acc>(ADD{std::move(a0)});
    }

    static std::shared_ptr<instr_acc> sub(unsigned int a0) {
      return std::make_shared<instr_acc>(SUB{std::move(a0)});
    }

    static std::shared_ptr<instr_acc> inc(unsigned int a0) {
      return std::make_shared<instr_acc>(INC{std::move(a0)});
    }

    static std::shared_ptr<instr_acc> xch(unsigned int a0) {
      return std::make_shared<instr_acc>(XCH{std::move(a0)});
    }

    static std::shared_ptr<instr_acc> bbl(unsigned int a0) {
      return std::make_shared<instr_acc>(BBL{std::move(a0)});
    }

    static std::shared_ptr<instr_acc> sbm() {
      return std::make_shared<instr_acc>(SBM{});
    }

    static std::shared_ptr<instr_acc> rdm() {
      return std::make_shared<instr_acc>(RDM{});
    }

    static std::shared_ptr<instr_acc> rdr() {
      return std::make_shared<instr_acc>(RDR{});
    }

    static std::shared_ptr<instr_acc> adm() {
      return std::make_shared<instr_acc>(ADM{});
    }

    static std::shared_ptr<instr_acc> rd0() {
      return std::make_shared<instr_acc>(RD0{});
    }

    static std::shared_ptr<instr_acc> rd1() {
      return std::make_shared<instr_acc>(RD1{});
    }

    static std::shared_ptr<instr_acc> rd2() {
      return std::make_shared<instr_acc>(RD2{});
    }

    static std::shared_ptr<instr_acc> rd3() {
      return std::make_shared<instr_acc>(RD3{});
    }

    static std::shared_ptr<instr_acc> clb() {
      return std::make_shared<instr_acc>(CLB{});
    }

    static std::shared_ptr<instr_acc> cma() {
      return std::make_shared<instr_acc>(CMA{});
    }

    static std::shared_ptr<instr_acc> iac() {
      return std::make_shared<instr_acc>(IAC{});
    }

    static std::shared_ptr<instr_acc> dac() {
      return std::make_shared<instr_acc>(DAC{});
    }

    static std::shared_ptr<instr_acc> ral() {
      return std::make_shared<instr_acc>(RAL{});
    }

    static std::shared_ptr<instr_acc> rar() {
      return std::make_shared<instr_acc>(RAR{});
    }

    static std::shared_ptr<instr_acc> tcc() {
      return std::make_shared<instr_acc>(TCC{});
    }

    static std::shared_ptr<instr_acc> tcs() {
      return std::make_shared<instr_acc>(TCS{});
    }

    static std::shared_ptr<instr_acc> daa() {
      return std::make_shared<instr_acc>(DAA{});
    }

    static std::shared_ptr<instr_acc> kbp() {
      return std::make_shared<instr_acc>(KBP{});
    }

    static std::shared_ptr<instr_acc> nop_acc() {
      return std::make_shared<instr_acc>(NOP_acc{});
    }

    static std::unique_ptr<instr_acc> ldm_uptr(unsigned int a0) {
      return std::make_unique<instr_acc>(LDM{std::move(a0)});
    }

    static std::unique_ptr<instr_acc> ld_uptr(unsigned int a0) {
      return std::make_unique<instr_acc>(LD{std::move(a0)});
    }

    static std::unique_ptr<instr_acc> add_uptr(unsigned int a0) {
      return std::make_unique<instr_acc>(ADD{std::move(a0)});
    }

    static std::unique_ptr<instr_acc> sub_uptr(unsigned int a0) {
      return std::make_unique<instr_acc>(SUB{std::move(a0)});
    }

    static std::unique_ptr<instr_acc> inc_uptr(unsigned int a0) {
      return std::make_unique<instr_acc>(INC{std::move(a0)});
    }

    static std::unique_ptr<instr_acc> xch_uptr(unsigned int a0) {
      return std::make_unique<instr_acc>(XCH{std::move(a0)});
    }

    static std::unique_ptr<instr_acc> bbl_uptr(unsigned int a0) {
      return std::make_unique<instr_acc>(BBL{std::move(a0)});
    }

    static std::unique_ptr<instr_acc> sbm_uptr() {
      return std::make_unique<instr_acc>(SBM{});
    }

    static std::unique_ptr<instr_acc> rdm_uptr() {
      return std::make_unique<instr_acc>(RDM{});
    }

    static std::unique_ptr<instr_acc> rdr_uptr() {
      return std::make_unique<instr_acc>(RDR{});
    }

    static std::unique_ptr<instr_acc> adm_uptr() {
      return std::make_unique<instr_acc>(ADM{});
    }

    static std::unique_ptr<instr_acc> rd0_uptr() {
      return std::make_unique<instr_acc>(RD0{});
    }

    static std::unique_ptr<instr_acc> rd1_uptr() {
      return std::make_unique<instr_acc>(RD1{});
    }

    static std::unique_ptr<instr_acc> rd2_uptr() {
      return std::make_unique<instr_acc>(RD2{});
    }

    static std::unique_ptr<instr_acc> rd3_uptr() {
      return std::make_unique<instr_acc>(RD3{});
    }

    static std::unique_ptr<instr_acc> clb_uptr() {
      return std::make_unique<instr_acc>(CLB{});
    }

    static std::unique_ptr<instr_acc> cma_uptr() {
      return std::make_unique<instr_acc>(CMA{});
    }

    static std::unique_ptr<instr_acc> iac_uptr() {
      return std::make_unique<instr_acc>(IAC{});
    }

    static std::unique_ptr<instr_acc> dac_uptr() {
      return std::make_unique<instr_acc>(DAC{});
    }

    static std::unique_ptr<instr_acc> ral_uptr() {
      return std::make_unique<instr_acc>(RAL{});
    }

    static std::unique_ptr<instr_acc> rar_uptr() {
      return std::make_unique<instr_acc>(RAR{});
    }

    static std::unique_ptr<instr_acc> tcc_uptr() {
      return std::make_unique<instr_acc>(TCC{});
    }

    static std::unique_ptr<instr_acc> tcs_uptr() {
      return std::make_unique<instr_acc>(TCS{});
    }

    static std::unique_ptr<instr_acc> daa_uptr() {
      return std::make_unique<instr_acc>(DAA{});
    }

    static std::unique_ptr<instr_acc> kbp_uptr() {
      return std::make_unique<instr_acc>(KBP{});
    }

    static std::unique_ptr<instr_acc> nop_acc_uptr() {
      return std::make_unique<instr_acc>(NOP_acc{});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    __attribute__((pure)) bool writes_acc() const {
      return std::visit(
          Overloaded{
              [](const typename instr_acc::LDM _args) -> bool { return true; },
              [](const typename instr_acc::LD _args) -> bool { return true; },
              [](const typename instr_acc::ADD _args) -> bool { return true; },
              [](const typename instr_acc::SUB _args) -> bool { return true; },
              [](const typename instr_acc::INC _args) -> bool { return true; },
              [](const typename instr_acc::XCH _args) -> bool { return true; },
              [](const typename instr_acc::BBL _args) -> bool { return true; },
              [](const typename instr_acc::SBM _args) -> bool { return true; },
              [](const typename instr_acc::RDM _args) -> bool { return true; },
              [](const typename instr_acc::RDR _args) -> bool { return true; },
              [](const typename instr_acc::ADM _args) -> bool { return true; },
              [](const typename instr_acc::RD0 _args) -> bool { return true; },
              [](const typename instr_acc::RD1 _args) -> bool { return true; },
              [](const typename instr_acc::RD2 _args) -> bool { return true; },
              [](const typename instr_acc::RD3 _args) -> bool { return true; },
              [](const typename instr_acc::CLB _args) -> bool { return true; },
              [](const typename instr_acc::CMA _args) -> bool { return true; },
              [](const typename instr_acc::IAC _args) -> bool { return true; },
              [](const typename instr_acc::DAC _args) -> bool { return true; },
              [](const typename instr_acc::RAL _args) -> bool { return true; },
              [](const typename instr_acc::RAR _args) -> bool { return true; },
              [](const typename instr_acc::TCC _args) -> bool { return true; },
              [](const typename instr_acc::TCS _args) -> bool { return true; },
              [](const typename instr_acc::DAA _args) -> bool { return true; },
              [](const typename instr_acc::KBP _args) -> bool { return true; },
              [](const typename instr_acc::NOP_acc _args) -> bool {
                return false;
              }},
          this->v());
    }

    template <typename T1, MapsTo<T1, unsigned int> F0,
              MapsTo<T1, unsigned int> F1, MapsTo<T1, unsigned int> F2,
              MapsTo<T1, unsigned int> F3, MapsTo<T1, unsigned int> F4,
              MapsTo<T1, unsigned int> F5, MapsTo<T1, unsigned int> F6>
    T1 instr_acc_rec(F0 &&f, F1 &&f0, F2 &&f1, F3 &&f2, F4 &&f3, F5 &&f4,
                     F6 &&f5, const T1 f6, const T1 f7, const T1 f8,
                     const T1 f9, const T1 f10, const T1 f11, const T1 f12,
                     const T1 f13, const T1 f14, const T1 f15, const T1 f16,
                     const T1 f17, const T1 f18, const T1 f19, const T1 f20,
                     const T1 f21, const T1 f22, const T1 f23,
                     const T1 f24) const {
      return std::visit(
          Overloaded{
              [&](const typename instr_acc::LDM _args) -> T1 {
                return f(_args.d_a0);
              },
              [&](const typename instr_acc::LD _args) -> T1 {
                return f0(_args.d_a0);
              },
              [&](const typename instr_acc::ADD _args) -> T1 {
                return f1(_args.d_a0);
              },
              [&](const typename instr_acc::SUB _args) -> T1 {
                return f2(_args.d_a0);
              },
              [&](const typename instr_acc::INC _args) -> T1 {
                return f3(_args.d_a0);
              },
              [&](const typename instr_acc::XCH _args) -> T1 {
                return f4(_args.d_a0);
              },
              [&](const typename instr_acc::BBL _args) -> T1 {
                return f5(_args.d_a0);
              },
              [&](const typename instr_acc::SBM _args) -> T1 { return f6; },
              [&](const typename instr_acc::RDM _args) -> T1 { return f7; },
              [&](const typename instr_acc::RDR _args) -> T1 { return f8; },
              [&](const typename instr_acc::ADM _args) -> T1 { return f9; },
              [&](const typename instr_acc::RD0 _args) -> T1 { return f10; },
              [&](const typename instr_acc::RD1 _args) -> T1 { return f11; },
              [&](const typename instr_acc::RD2 _args) -> T1 { return f12; },
              [&](const typename instr_acc::RD3 _args) -> T1 { return f13; },
              [&](const typename instr_acc::CLB _args) -> T1 { return f14; },
              [&](const typename instr_acc::CMA _args) -> T1 { return f15; },
              [&](const typename instr_acc::IAC _args) -> T1 { return f16; },
              [&](const typename instr_acc::DAC _args) -> T1 { return f17; },
              [&](const typename instr_acc::RAL _args) -> T1 { return f18; },
              [&](const typename instr_acc::RAR _args) -> T1 { return f19; },
              [&](const typename instr_acc::TCC _args) -> T1 { return f20; },
              [&](const typename instr_acc::TCS _args) -> T1 { return f21; },
              [&](const typename instr_acc::DAA _args) -> T1 { return f22; },
              [&](const typename instr_acc::KBP _args) -> T1 { return f23; },
              [&](const typename instr_acc::NOP_acc _args) -> T1 {
                return f24;
              }},
          this->v());
    }

    template <typename T1, MapsTo<T1, unsigned int> F0,
              MapsTo<T1, unsigned int> F1, MapsTo<T1, unsigned int> F2,
              MapsTo<T1, unsigned int> F3, MapsTo<T1, unsigned int> F4,
              MapsTo<T1, unsigned int> F5, MapsTo<T1, unsigned int> F6>
    T1 instr_acc_rect(F0 &&f, F1 &&f0, F2 &&f1, F3 &&f2, F4 &&f3, F5 &&f4,
                      F6 &&f5, const T1 f6, const T1 f7, const T1 f8,
                      const T1 f9, const T1 f10, const T1 f11, const T1 f12,
                      const T1 f13, const T1 f14, const T1 f15, const T1 f16,
                      const T1 f17, const T1 f18, const T1 f19, const T1 f20,
                      const T1 f21, const T1 f22, const T1 f23,
                      const T1 f24) const {
      return std::visit(
          Overloaded{
              [&](const typename instr_acc::LDM _args) -> T1 {
                return f(_args.d_a0);
              },
              [&](const typename instr_acc::LD _args) -> T1 {
                return f0(_args.d_a0);
              },
              [&](const typename instr_acc::ADD _args) -> T1 {
                return f1(_args.d_a0);
              },
              [&](const typename instr_acc::SUB _args) -> T1 {
                return f2(_args.d_a0);
              },
              [&](const typename instr_acc::INC _args) -> T1 {
                return f3(_args.d_a0);
              },
              [&](const typename instr_acc::XCH _args) -> T1 {
                return f4(_args.d_a0);
              },
              [&](const typename instr_acc::BBL _args) -> T1 {
                return f5(_args.d_a0);
              },
              [&](const typename instr_acc::SBM _args) -> T1 { return f6; },
              [&](const typename instr_acc::RDM _args) -> T1 { return f7; },
              [&](const typename instr_acc::RDR _args) -> T1 { return f8; },
              [&](const typename instr_acc::ADM _args) -> T1 { return f9; },
              [&](const typename instr_acc::RD0 _args) -> T1 { return f10; },
              [&](const typename instr_acc::RD1 _args) -> T1 { return f11; },
              [&](const typename instr_acc::RD2 _args) -> T1 { return f12; },
              [&](const typename instr_acc::RD3 _args) -> T1 { return f13; },
              [&](const typename instr_acc::CLB _args) -> T1 { return f14; },
              [&](const typename instr_acc::CMA _args) -> T1 { return f15; },
              [&](const typename instr_acc::IAC _args) -> T1 { return f16; },
              [&](const typename instr_acc::DAC _args) -> T1 { return f17; },
              [&](const typename instr_acc::RAL _args) -> T1 { return f18; },
              [&](const typename instr_acc::RAR _args) -> T1 { return f19; },
              [&](const typename instr_acc::TCC _args) -> T1 { return f20; },
              [&](const typename instr_acc::TCS _args) -> T1 { return f21; },
              [&](const typename instr_acc::DAA _args) -> T1 { return f22; },
              [&](const typename instr_acc::KBP _args) -> T1 { return f23; },
              [&](const typename instr_acc::NOP_acc _args) -> T1 {
                return f24;
              }},
          this->v());
    }
  };

  __attribute__((pure)) static unsigned int count_writes_acc(
      const std::shared_ptr<List<std::shared_ptr<instr_acc>>> &prog);
  static inline const unsigned int test_writes_acc =
      count_writes_acc(List<std::shared_ptr<instr_acc>>::cons(
          instr_acc::nop_acc(),
          List<std::shared_ptr<instr_acc>>::cons(
              instr_acc::ldm(9u),
              List<std::shared_ptr<instr_acc>>::cons(
                  instr_acc::rar(),
                  List<std::shared_ptr<instr_acc>>::cons(
                      instr_acc::kbp(),
                      List<std::shared_ptr<instr_acc>>::cons(
                          instr_acc::nop_acc(),
                          List<std::shared_ptr<instr_acc>>::cons(
                              instr_acc::add(1u),
                              List<std::shared_ptr<instr_acc>>::nil())))))));

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
      unsigned int d_a0;
    };

    using variant_t =
        std::variant<WRM, WMP, WR0, WR1, WR2, WR3, NOP_ram, ADD_ram>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    explicit instr_ram(WRM _v) : d_v_(std::move(_v)) {}

    explicit instr_ram(WMP _v) : d_v_(std::move(_v)) {}

    explicit instr_ram(WR0 _v) : d_v_(std::move(_v)) {}

    explicit instr_ram(WR1 _v) : d_v_(std::move(_v)) {}

    explicit instr_ram(WR2 _v) : d_v_(std::move(_v)) {}

    explicit instr_ram(WR3 _v) : d_v_(std::move(_v)) {}

    explicit instr_ram(NOP_ram _v) : d_v_(std::move(_v)) {}

    explicit instr_ram(ADD_ram _v) : d_v_(std::move(_v)) {}

    static std::shared_ptr<instr_ram> wrm() {
      return std::make_shared<instr_ram>(WRM{});
    }

    static std::shared_ptr<instr_ram> wmp() {
      return std::make_shared<instr_ram>(WMP{});
    }

    static std::shared_ptr<instr_ram> wr0() {
      return std::make_shared<instr_ram>(WR0{});
    }

    static std::shared_ptr<instr_ram> wr1() {
      return std::make_shared<instr_ram>(WR1{});
    }

    static std::shared_ptr<instr_ram> wr2() {
      return std::make_shared<instr_ram>(WR2{});
    }

    static std::shared_ptr<instr_ram> wr3() {
      return std::make_shared<instr_ram>(WR3{});
    }

    static std::shared_ptr<instr_ram> nop_ram() {
      return std::make_shared<instr_ram>(NOP_ram{});
    }

    static std::shared_ptr<instr_ram> add_ram(unsigned int a0) {
      return std::make_shared<instr_ram>(ADD_ram{std::move(a0)});
    }

    static std::unique_ptr<instr_ram> wrm_uptr() {
      return std::make_unique<instr_ram>(WRM{});
    }

    static std::unique_ptr<instr_ram> wmp_uptr() {
      return std::make_unique<instr_ram>(WMP{});
    }

    static std::unique_ptr<instr_ram> wr0_uptr() {
      return std::make_unique<instr_ram>(WR0{});
    }

    static std::unique_ptr<instr_ram> wr1_uptr() {
      return std::make_unique<instr_ram>(WR1{});
    }

    static std::unique_ptr<instr_ram> wr2_uptr() {
      return std::make_unique<instr_ram>(WR2{});
    }

    static std::unique_ptr<instr_ram> wr3_uptr() {
      return std::make_unique<instr_ram>(WR3{});
    }

    static std::unique_ptr<instr_ram> nop_ram_uptr() {
      return std::make_unique<instr_ram>(NOP_ram{});
    }

    static std::unique_ptr<instr_ram> add_ram_uptr(unsigned int a0) {
      return std::make_unique<instr_ram>(ADD_ram{std::move(a0)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    __attribute__((pure)) bool writes_ram() const {
      return std::visit(
          Overloaded{
              [](const typename instr_ram::WRM _args) -> bool { return true; },
              [](const typename instr_ram::WMP _args) -> bool { return true; },
              [](const typename instr_ram::WR0 _args) -> bool { return true; },
              [](const typename instr_ram::WR1 _args) -> bool { return true; },
              [](const typename instr_ram::WR2 _args) -> bool { return true; },
              [](const typename instr_ram::WR3 _args) -> bool { return true; },
              [](const typename instr_ram::NOP_ram _args) -> bool {
                return false;
              },
              [](const typename instr_ram::ADD_ram _args) -> bool {
                return false;
              }},
          this->v());
    }
  };

  template <typename T1, MapsTo<T1, unsigned int> F7>
  static T1 instr_ram_rect(const T1 f, const T1 f0, const T1 f1, const T1 f2,
                           const T1 f3, const T1 f4, const T1 f5, F7 &&f6,
                           const std::shared_ptr<instr_ram> &i) {
    return std::visit(
        Overloaded{
            [&](const typename instr_ram::WRM _args) -> T1 { return f; },
            [&](const typename instr_ram::WMP _args) -> T1 { return f0; },
            [&](const typename instr_ram::WR0 _args) -> T1 { return f1; },
            [&](const typename instr_ram::WR1 _args) -> T1 { return f2; },
            [&](const typename instr_ram::WR2 _args) -> T1 { return f3; },
            [&](const typename instr_ram::WR3 _args) -> T1 { return f4; },
            [&](const typename instr_ram::NOP_ram _args) -> T1 { return f5; },
            [&](const typename instr_ram::ADD_ram _args) -> T1 {
              return f6(_args.d_a0);
            }},
        i->v());
  }

  template <typename T1, MapsTo<T1, unsigned int> F7>
  static T1 instr_ram_rec(const T1 f, const T1 f0, const T1 f1, const T1 f2,
                          const T1 f3, const T1 f4, const T1 f5, F7 &&f6,
                          const std::shared_ptr<instr_ram> &i) {
    return std::visit(
        Overloaded{
            [&](const typename instr_ram::WRM _args) -> T1 { return f; },
            [&](const typename instr_ram::WMP _args) -> T1 { return f0; },
            [&](const typename instr_ram::WR0 _args) -> T1 { return f1; },
            [&](const typename instr_ram::WR1 _args) -> T1 { return f2; },
            [&](const typename instr_ram::WR2 _args) -> T1 { return f3; },
            [&](const typename instr_ram::WR3 _args) -> T1 { return f4; },
            [&](const typename instr_ram::NOP_ram _args) -> T1 { return f5; },
            [&](const typename instr_ram::ADD_ram _args) -> T1 {
              return f6(_args.d_a0);
            }},
        i->v());
  }

  __attribute__((pure)) static unsigned int count_writes_ram(
      const std::shared_ptr<List<std::shared_ptr<instr_ram>>> &prog);
  static inline const unsigned int test_writes_ram =
      count_writes_ram(List<std::shared_ptr<instr_ram>>::cons(
          instr_ram::nop_ram(),
          List<std::shared_ptr<instr_ram>>::cons(
              instr_ram::wrm(),
              List<std::shared_ptr<instr_ram>>::cons(
                  instr_ram::add_ram(3u),
                  List<std::shared_ptr<instr_ram>>::cons(
                      instr_ram::wr3(),
                      List<std::shared_ptr<instr_ram>>::cons(
                          instr_ram::wmp(),
                          List<std::shared_ptr<instr_ram>>::cons(
                              instr_ram::nop_ram(),
                              List<std::shared_ptr<instr_ram>>::nil())))))));

  struct instr_regs {
    // TYPES
    struct XCH_regs {
      unsigned int d_a0;
    };

    struct INC_regs {
      unsigned int d_a0;
    };

    struct FIM {
      unsigned int d_a0;
      unsigned int d_a1;
    };

    struct FIN {
      unsigned int d_a0;
    };

    struct ISZ {
      unsigned int d_a0;
      unsigned int d_a1;
    };

    struct NOP_regs {};

    struct ADD_regs {
      unsigned int d_a0;
    };

    using variant_t =
        std::variant<XCH_regs, INC_regs, FIM, FIN, ISZ, NOP_regs, ADD_regs>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    explicit instr_regs(XCH_regs _v) : d_v_(std::move(_v)) {}

    explicit instr_regs(INC_regs _v) : d_v_(std::move(_v)) {}

    explicit instr_regs(FIM _v) : d_v_(std::move(_v)) {}

    explicit instr_regs(FIN _v) : d_v_(std::move(_v)) {}

    explicit instr_regs(ISZ _v) : d_v_(std::move(_v)) {}

    explicit instr_regs(NOP_regs _v) : d_v_(std::move(_v)) {}

    explicit instr_regs(ADD_regs _v) : d_v_(std::move(_v)) {}

    static std::shared_ptr<instr_regs> xch_regs(unsigned int a0) {
      return std::make_shared<instr_regs>(XCH_regs{std::move(a0)});
    }

    static std::shared_ptr<instr_regs> inc_regs(unsigned int a0) {
      return std::make_shared<instr_regs>(INC_regs{std::move(a0)});
    }

    static std::shared_ptr<instr_regs> fim(unsigned int a0, unsigned int a1) {
      return std::make_shared<instr_regs>(FIM{std::move(a0), std::move(a1)});
    }

    static std::shared_ptr<instr_regs> fin(unsigned int a0) {
      return std::make_shared<instr_regs>(FIN{std::move(a0)});
    }

    static std::shared_ptr<instr_regs> isz(unsigned int a0, unsigned int a1) {
      return std::make_shared<instr_regs>(ISZ{std::move(a0), std::move(a1)});
    }

    static std::shared_ptr<instr_regs> nop_regs() {
      return std::make_shared<instr_regs>(NOP_regs{});
    }

    static std::shared_ptr<instr_regs> add_regs(unsigned int a0) {
      return std::make_shared<instr_regs>(ADD_regs{std::move(a0)});
    }

    static std::unique_ptr<instr_regs> xch_regs_uptr(unsigned int a0) {
      return std::make_unique<instr_regs>(XCH_regs{std::move(a0)});
    }

    static std::unique_ptr<instr_regs> inc_regs_uptr(unsigned int a0) {
      return std::make_unique<instr_regs>(INC_regs{std::move(a0)});
    }

    static std::unique_ptr<instr_regs> fim_uptr(unsigned int a0,
                                                unsigned int a1) {
      return std::make_unique<instr_regs>(FIM{std::move(a0), std::move(a1)});
    }

    static std::unique_ptr<instr_regs> fin_uptr(unsigned int a0) {
      return std::make_unique<instr_regs>(FIN{std::move(a0)});
    }

    static std::unique_ptr<instr_regs> isz_uptr(unsigned int a0,
                                                unsigned int a1) {
      return std::make_unique<instr_regs>(ISZ{std::move(a0), std::move(a1)});
    }

    static std::unique_ptr<instr_regs> nop_regs_uptr() {
      return std::make_unique<instr_regs>(NOP_regs{});
    }

    static std::unique_ptr<instr_regs> add_regs_uptr(unsigned int a0) {
      return std::make_unique<instr_regs>(ADD_regs{std::move(a0)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    __attribute__((pure)) bool writes_regs() const {
      return std::visit(
          Overloaded{
              [](const typename instr_regs::XCH_regs _args) -> bool {
                return true;
              },
              [](const typename instr_regs::INC_regs _args) -> bool {
                return true;
              },
              [](const typename instr_regs::FIM _args) -> bool { return true; },
              [](const typename instr_regs::FIN _args) -> bool { return true; },
              [](const typename instr_regs::ISZ _args) -> bool { return true; },
              [](const typename instr_regs::NOP_regs _args) -> bool {
                return false;
              },
              [](const typename instr_regs::ADD_regs _args) -> bool {
                return false;
              }},
          this->v());
    }

    template <
        typename T1, MapsTo<T1, unsigned int> F0, MapsTo<T1, unsigned int> F1,
        MapsTo<T1, unsigned int, unsigned int> F2, MapsTo<T1, unsigned int> F3,
        MapsTo<T1, unsigned int, unsigned int> F4, MapsTo<T1, unsigned int> F6>
    T1 instr_regs_rec(F0 &&f, F1 &&f0, F2 &&f1, F3 &&f2, F4 &&f3, const T1 f4,
                      F6 &&f5) const {
      return std::visit(
          Overloaded{[&](const typename instr_regs::XCH_regs _args) -> T1 {
                       return f(_args.d_a0);
                     },
                     [&](const typename instr_regs::INC_regs _args) -> T1 {
                       return f0(_args.d_a0);
                     },
                     [&](const typename instr_regs::FIM _args) -> T1 {
                       return f1(_args.d_a0, _args.d_a1);
                     },
                     [&](const typename instr_regs::FIN _args) -> T1 {
                       return f2(_args.d_a0);
                     },
                     [&](const typename instr_regs::ISZ _args) -> T1 {
                       return f3(_args.d_a0, _args.d_a1);
                     },
                     [&](const typename instr_regs::NOP_regs _args) -> T1 {
                       return f4;
                     },
                     [&](const typename instr_regs::ADD_regs _args) -> T1 {
                       return f5(_args.d_a0);
                     }},
          this->v());
    }

    template <
        typename T1, MapsTo<T1, unsigned int> F0, MapsTo<T1, unsigned int> F1,
        MapsTo<T1, unsigned int, unsigned int> F2, MapsTo<T1, unsigned int> F3,
        MapsTo<T1, unsigned int, unsigned int> F4, MapsTo<T1, unsigned int> F6>
    T1 instr_regs_rect(F0 &&f, F1 &&f0, F2 &&f1, F3 &&f2, F4 &&f3, const T1 f4,
                       F6 &&f5) const {
      return std::visit(
          Overloaded{[&](const typename instr_regs::XCH_regs _args) -> T1 {
                       return f(_args.d_a0);
                     },
                     [&](const typename instr_regs::INC_regs _args) -> T1 {
                       return f0(_args.d_a0);
                     },
                     [&](const typename instr_regs::FIM _args) -> T1 {
                       return f1(_args.d_a0, _args.d_a1);
                     },
                     [&](const typename instr_regs::FIN _args) -> T1 {
                       return f2(_args.d_a0);
                     },
                     [&](const typename instr_regs::ISZ _args) -> T1 {
                       return f3(_args.d_a0, _args.d_a1);
                     },
                     [&](const typename instr_regs::NOP_regs _args) -> T1 {
                       return f4;
                     },
                     [&](const typename instr_regs::ADD_regs _args) -> T1 {
                       return f5(_args.d_a0);
                     }},
          this->v());
    }
  };

  __attribute__((pure)) static unsigned int count_writes_regs(
      const std::shared_ptr<List<std::shared_ptr<instr_regs>>> &prog);
  static inline const unsigned int test_writes_regs =
      count_writes_regs(List<std::shared_ptr<instr_regs>>::cons(
          instr_regs::nop_regs(),
          List<std::shared_ptr<instr_regs>>::cons(
              instr_regs::fim(0u, 12u),
              List<std::shared_ptr<instr_regs>>::cons(
                  instr_regs::add_regs(1u),
                  List<std::shared_ptr<instr_regs>>::cons(
                      instr_regs::inc_regs(7u),
                      List<std::shared_ptr<instr_regs>>::cons(
                          instr_regs::isz(1u, 2u),
                          List<std::shared_ptr<instr_regs>>::nil()))))));

  struct instr_jump {
    // TYPES
    struct JCN {
      unsigned int d_a0;
      unsigned int d_a1;
    };

    struct JUN {
      unsigned int d_a0;
    };

    struct JMS {
      unsigned int d_a0;
    };

    struct JIN {
      unsigned int d_a0;
    };

    struct BBL_jump {
      unsigned int d_a0;
    };

    struct ISZ_jump {
      unsigned int d_a0;
      unsigned int d_a1;
    };

    struct ADD_jump {
      unsigned int d_a0;
    };

    struct NOP_jump {};

    using variant_t = std::variant<JCN, JUN, JMS, JIN, BBL_jump, ISZ_jump,
                                   ADD_jump, NOP_jump>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    explicit instr_jump(JCN _v) : d_v_(std::move(_v)) {}

    explicit instr_jump(JUN _v) : d_v_(std::move(_v)) {}

    explicit instr_jump(JMS _v) : d_v_(std::move(_v)) {}

    explicit instr_jump(JIN _v) : d_v_(std::move(_v)) {}

    explicit instr_jump(BBL_jump _v) : d_v_(std::move(_v)) {}

    explicit instr_jump(ISZ_jump _v) : d_v_(std::move(_v)) {}

    explicit instr_jump(ADD_jump _v) : d_v_(std::move(_v)) {}

    explicit instr_jump(NOP_jump _v) : d_v_(std::move(_v)) {}

    static std::shared_ptr<instr_jump> jcn(unsigned int a0, unsigned int a1) {
      return std::make_shared<instr_jump>(JCN{std::move(a0), std::move(a1)});
    }

    static std::shared_ptr<instr_jump> jun(unsigned int a0) {
      return std::make_shared<instr_jump>(JUN{std::move(a0)});
    }

    static std::shared_ptr<instr_jump> jms(unsigned int a0) {
      return std::make_shared<instr_jump>(JMS{std::move(a0)});
    }

    static std::shared_ptr<instr_jump> jin(unsigned int a0) {
      return std::make_shared<instr_jump>(JIN{std::move(a0)});
    }

    static std::shared_ptr<instr_jump> bbl_jump(unsigned int a0) {
      return std::make_shared<instr_jump>(BBL_jump{std::move(a0)});
    }

    static std::shared_ptr<instr_jump> isz_jump(unsigned int a0,
                                                unsigned int a1) {
      return std::make_shared<instr_jump>(
          ISZ_jump{std::move(a0), std::move(a1)});
    }

    static std::shared_ptr<instr_jump> add_jump(unsigned int a0) {
      return std::make_shared<instr_jump>(ADD_jump{std::move(a0)});
    }

    static std::shared_ptr<instr_jump> nop_jump() {
      return std::make_shared<instr_jump>(NOP_jump{});
    }

    static std::unique_ptr<instr_jump> jcn_uptr(unsigned int a0,
                                                unsigned int a1) {
      return std::make_unique<instr_jump>(JCN{std::move(a0), std::move(a1)});
    }

    static std::unique_ptr<instr_jump> jun_uptr(unsigned int a0) {
      return std::make_unique<instr_jump>(JUN{std::move(a0)});
    }

    static std::unique_ptr<instr_jump> jms_uptr(unsigned int a0) {
      return std::make_unique<instr_jump>(JMS{std::move(a0)});
    }

    static std::unique_ptr<instr_jump> jin_uptr(unsigned int a0) {
      return std::make_unique<instr_jump>(JIN{std::move(a0)});
    }

    static std::unique_ptr<instr_jump> bbl_jump_uptr(unsigned int a0) {
      return std::make_unique<instr_jump>(BBL_jump{std::move(a0)});
    }

    static std::unique_ptr<instr_jump> isz_jump_uptr(unsigned int a0,
                                                     unsigned int a1) {
      return std::make_unique<instr_jump>(
          ISZ_jump{std::move(a0), std::move(a1)});
    }

    static std::unique_ptr<instr_jump> add_jump_uptr(unsigned int a0) {
      return std::make_unique<instr_jump>(ADD_jump{std::move(a0)});
    }

    static std::unique_ptr<instr_jump> nop_jump_uptr() {
      return std::make_unique<instr_jump>(NOP_jump{});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    __attribute__((pure)) bool is_jump() const {
      return std::visit(
          Overloaded{
              [](const typename instr_jump::JCN _args) -> bool { return true; },
              [](const typename instr_jump::JUN _args) -> bool { return true; },
              [](const typename instr_jump::JMS _args) -> bool { return true; },
              [](const typename instr_jump::JIN _args) -> bool { return true; },
              [](const typename instr_jump::BBL_jump _args) -> bool {
                return true;
              },
              [](const typename instr_jump::ISZ_jump _args) -> bool {
                return true;
              },
              [](const typename instr_jump::ADD_jump _args) -> bool {
                return false;
              },
              [](const typename instr_jump::NOP_jump _args) -> bool {
                return false;
              }},
          this->v());
    }

    template <typename T1, MapsTo<T1, unsigned int, unsigned int> F0,
              MapsTo<T1, unsigned int> F1, MapsTo<T1, unsigned int> F2,
              MapsTo<T1, unsigned int> F3, MapsTo<T1, unsigned int> F4,
              MapsTo<T1, unsigned int, unsigned int> F5,
              MapsTo<T1, unsigned int> F6>
    T1 instr_jump_rec(F0 &&f, F1 &&f0, F2 &&f1, F3 &&f2, F4 &&f3, F5 &&f4,
                      F6 &&f5, const T1 f6) const {
      return std::visit(
          Overloaded{[&](const typename instr_jump::JCN _args) -> T1 {
                       return f(_args.d_a0, _args.d_a1);
                     },
                     [&](const typename instr_jump::JUN _args) -> T1 {
                       return f0(_args.d_a0);
                     },
                     [&](const typename instr_jump::JMS _args) -> T1 {
                       return f1(_args.d_a0);
                     },
                     [&](const typename instr_jump::JIN _args) -> T1 {
                       return f2(_args.d_a0);
                     },
                     [&](const typename instr_jump::BBL_jump _args) -> T1 {
                       return f3(_args.d_a0);
                     },
                     [&](const typename instr_jump::ISZ_jump _args) -> T1 {
                       return f4(_args.d_a0, _args.d_a1);
                     },
                     [&](const typename instr_jump::ADD_jump _args) -> T1 {
                       return f5(_args.d_a0);
                     },
                     [&](const typename instr_jump::NOP_jump _args) -> T1 {
                       return f6;
                     }},
          this->v());
    }

    template <typename T1, MapsTo<T1, unsigned int, unsigned int> F0,
              MapsTo<T1, unsigned int> F1, MapsTo<T1, unsigned int> F2,
              MapsTo<T1, unsigned int> F3, MapsTo<T1, unsigned int> F4,
              MapsTo<T1, unsigned int, unsigned int> F5,
              MapsTo<T1, unsigned int> F6>
    T1 instr_jump_rect(F0 &&f, F1 &&f0, F2 &&f1, F3 &&f2, F4 &&f3, F5 &&f4,
                       F6 &&f5, const T1 f6) const {
      return std::visit(
          Overloaded{[&](const typename instr_jump::JCN _args) -> T1 {
                       return f(_args.d_a0, _args.d_a1);
                     },
                     [&](const typename instr_jump::JUN _args) -> T1 {
                       return f0(_args.d_a0);
                     },
                     [&](const typename instr_jump::JMS _args) -> T1 {
                       return f1(_args.d_a0);
                     },
                     [&](const typename instr_jump::JIN _args) -> T1 {
                       return f2(_args.d_a0);
                     },
                     [&](const typename instr_jump::BBL_jump _args) -> T1 {
                       return f3(_args.d_a0);
                     },
                     [&](const typename instr_jump::ISZ_jump _args) -> T1 {
                       return f4(_args.d_a0, _args.d_a1);
                     },
                     [&](const typename instr_jump::ADD_jump _args) -> T1 {
                       return f5(_args.d_a0);
                     },
                     [&](const typename instr_jump::NOP_jump _args) -> T1 {
                       return f6;
                     }},
          this->v());
    }
  };

  __attribute__((pure)) static unsigned int
  count_jumps(const std::shared_ptr<List<std::shared_ptr<instr_jump>>> &prog);
  static inline const unsigned int test_jump_classifier =
      count_jumps(List<std::shared_ptr<instr_jump>>::cons(
          instr_jump::add_jump(0u),
          List<std::shared_ptr<instr_jump>>::cons(
              instr_jump::jcn(4u, 8u),
              List<std::shared_ptr<instr_jump>>::cons(
                  instr_jump::nop_jump(),
                  List<std::shared_ptr<instr_jump>>::cons(
                      instr_jump::jms(33u),
                      List<std::shared_ptr<instr_jump>>::cons(
                          instr_jump::isz_jump(1u, 2u),
                          List<std::shared_ptr<instr_jump>>::nil()))))));
  static inline const std::pair<
      std::pair<std::pair<unsigned int, unsigned int>, unsigned int>,
      unsigned int>
      t = std::make_pair(
          std::make_pair(std::make_pair(test_writes_acc, test_writes_ram),
                         test_writes_regs),
          test_jump_classifier);
};

#endif // INCLUDED_INSTRUCTION_CLASSIFIERS
