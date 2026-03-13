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

  public:
    // TYPES
    struct ctor {
      ctor() = delete;

      static std::shared_ptr<instr_acc> LDM_(unsigned int a0) {
        return std::shared_ptr<instr_acc>(new instr_acc(LDM{a0}));
      }

      static std::shared_ptr<instr_acc> LD_(unsigned int a0) {
        return std::shared_ptr<instr_acc>(new instr_acc(LD{a0}));
      }

      static std::shared_ptr<instr_acc> ADD_(unsigned int a0) {
        return std::shared_ptr<instr_acc>(new instr_acc(ADD{a0}));
      }

      static std::shared_ptr<instr_acc> SUB_(unsigned int a0) {
        return std::shared_ptr<instr_acc>(new instr_acc(SUB{a0}));
      }

      static std::shared_ptr<instr_acc> INC_(unsigned int a0) {
        return std::shared_ptr<instr_acc>(new instr_acc(INC{a0}));
      }

      static std::shared_ptr<instr_acc> XCH_(unsigned int a0) {
        return std::shared_ptr<instr_acc>(new instr_acc(XCH{a0}));
      }

      static std::shared_ptr<instr_acc> BBL_(unsigned int a0) {
        return std::shared_ptr<instr_acc>(new instr_acc(BBL{a0}));
      }

      static std::shared_ptr<instr_acc> SBM_() {
        return std::shared_ptr<instr_acc>(new instr_acc(SBM{}));
      }

      static std::shared_ptr<instr_acc> RDM_() {
        return std::shared_ptr<instr_acc>(new instr_acc(RDM{}));
      }

      static std::shared_ptr<instr_acc> RDR_() {
        return std::shared_ptr<instr_acc>(new instr_acc(RDR{}));
      }

      static std::shared_ptr<instr_acc> ADM_() {
        return std::shared_ptr<instr_acc>(new instr_acc(ADM{}));
      }

      static std::shared_ptr<instr_acc> RD0_() {
        return std::shared_ptr<instr_acc>(new instr_acc(RD0{}));
      }

      static std::shared_ptr<instr_acc> RD1_() {
        return std::shared_ptr<instr_acc>(new instr_acc(RD1{}));
      }

      static std::shared_ptr<instr_acc> RD2_() {
        return std::shared_ptr<instr_acc>(new instr_acc(RD2{}));
      }

      static std::shared_ptr<instr_acc> RD3_() {
        return std::shared_ptr<instr_acc>(new instr_acc(RD3{}));
      }

      static std::shared_ptr<instr_acc> CLB_() {
        return std::shared_ptr<instr_acc>(new instr_acc(CLB{}));
      }

      static std::shared_ptr<instr_acc> CMA_() {
        return std::shared_ptr<instr_acc>(new instr_acc(CMA{}));
      }

      static std::shared_ptr<instr_acc> IAC_() {
        return std::shared_ptr<instr_acc>(new instr_acc(IAC{}));
      }

      static std::shared_ptr<instr_acc> DAC_() {
        return std::shared_ptr<instr_acc>(new instr_acc(DAC{}));
      }

      static std::shared_ptr<instr_acc> RAL_() {
        return std::shared_ptr<instr_acc>(new instr_acc(RAL{}));
      }

      static std::shared_ptr<instr_acc> RAR_() {
        return std::shared_ptr<instr_acc>(new instr_acc(RAR{}));
      }

      static std::shared_ptr<instr_acc> TCC_() {
        return std::shared_ptr<instr_acc>(new instr_acc(TCC{}));
      }

      static std::shared_ptr<instr_acc> TCS_() {
        return std::shared_ptr<instr_acc>(new instr_acc(TCS{}));
      }

      static std::shared_ptr<instr_acc> DAA_() {
        return std::shared_ptr<instr_acc>(new instr_acc(DAA{}));
      }

      static std::shared_ptr<instr_acc> KBP_() {
        return std::shared_ptr<instr_acc>(new instr_acc(KBP{}));
      }

      static std::shared_ptr<instr_acc> NOP_acc_() {
        return std::shared_ptr<instr_acc>(new instr_acc(NOP_acc{}));
      }

      static std::unique_ptr<instr_acc> LDM_uptr(unsigned int a0) {
        return std::unique_ptr<instr_acc>(new instr_acc(LDM{a0}));
      }

      static std::unique_ptr<instr_acc> LD_uptr(unsigned int a0) {
        return std::unique_ptr<instr_acc>(new instr_acc(LD{a0}));
      }

      static std::unique_ptr<instr_acc> ADD_uptr(unsigned int a0) {
        return std::unique_ptr<instr_acc>(new instr_acc(ADD{a0}));
      }

      static std::unique_ptr<instr_acc> SUB_uptr(unsigned int a0) {
        return std::unique_ptr<instr_acc>(new instr_acc(SUB{a0}));
      }

      static std::unique_ptr<instr_acc> INC_uptr(unsigned int a0) {
        return std::unique_ptr<instr_acc>(new instr_acc(INC{a0}));
      }

      static std::unique_ptr<instr_acc> XCH_uptr(unsigned int a0) {
        return std::unique_ptr<instr_acc>(new instr_acc(XCH{a0}));
      }

      static std::unique_ptr<instr_acc> BBL_uptr(unsigned int a0) {
        return std::unique_ptr<instr_acc>(new instr_acc(BBL{a0}));
      }

      static std::unique_ptr<instr_acc> SBM_uptr() {
        return std::unique_ptr<instr_acc>(new instr_acc(SBM{}));
      }

      static std::unique_ptr<instr_acc> RDM_uptr() {
        return std::unique_ptr<instr_acc>(new instr_acc(RDM{}));
      }

      static std::unique_ptr<instr_acc> RDR_uptr() {
        return std::unique_ptr<instr_acc>(new instr_acc(RDR{}));
      }

      static std::unique_ptr<instr_acc> ADM_uptr() {
        return std::unique_ptr<instr_acc>(new instr_acc(ADM{}));
      }

      static std::unique_ptr<instr_acc> RD0_uptr() {
        return std::unique_ptr<instr_acc>(new instr_acc(RD0{}));
      }

      static std::unique_ptr<instr_acc> RD1_uptr() {
        return std::unique_ptr<instr_acc>(new instr_acc(RD1{}));
      }

      static std::unique_ptr<instr_acc> RD2_uptr() {
        return std::unique_ptr<instr_acc>(new instr_acc(RD2{}));
      }

      static std::unique_ptr<instr_acc> RD3_uptr() {
        return std::unique_ptr<instr_acc>(new instr_acc(RD3{}));
      }

      static std::unique_ptr<instr_acc> CLB_uptr() {
        return std::unique_ptr<instr_acc>(new instr_acc(CLB{}));
      }

      static std::unique_ptr<instr_acc> CMA_uptr() {
        return std::unique_ptr<instr_acc>(new instr_acc(CMA{}));
      }

      static std::unique_ptr<instr_acc> IAC_uptr() {
        return std::unique_ptr<instr_acc>(new instr_acc(IAC{}));
      }

      static std::unique_ptr<instr_acc> DAC_uptr() {
        return std::unique_ptr<instr_acc>(new instr_acc(DAC{}));
      }

      static std::unique_ptr<instr_acc> RAL_uptr() {
        return std::unique_ptr<instr_acc>(new instr_acc(RAL{}));
      }

      static std::unique_ptr<instr_acc> RAR_uptr() {
        return std::unique_ptr<instr_acc>(new instr_acc(RAR{}));
      }

      static std::unique_ptr<instr_acc> TCC_uptr() {
        return std::unique_ptr<instr_acc>(new instr_acc(TCC{}));
      }

      static std::unique_ptr<instr_acc> TCS_uptr() {
        return std::unique_ptr<instr_acc>(new instr_acc(TCS{}));
      }

      static std::unique_ptr<instr_acc> DAA_uptr() {
        return std::unique_ptr<instr_acc>(new instr_acc(DAA{}));
      }

      static std::unique_ptr<instr_acc> KBP_uptr() {
        return std::unique_ptr<instr_acc>(new instr_acc(KBP{}));
      }

      static std::unique_ptr<instr_acc> NOP_acc_uptr() {
        return std::unique_ptr<instr_acc>(new instr_acc(NOP_acc{}));
      }
    };

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, MapsTo<T1, unsigned int> F0,
            MapsTo<T1, unsigned int> F1, MapsTo<T1, unsigned int> F2,
            MapsTo<T1, unsigned int> F3, MapsTo<T1, unsigned int> F4,
            MapsTo<T1, unsigned int> F5, MapsTo<T1, unsigned int> F6>
  static T1 instr_acc_rect(F0 &&f, F1 &&f0, F2 &&f1, F3 &&f2, F4 &&f3, F5 &&f4,
                           F6 &&f5, const T1 f6, const T1 f7, const T1 f8,
                           const T1 f9, const T1 f10, const T1 f11,
                           const T1 f12, const T1 f13, const T1 f14,
                           const T1 f15, const T1 f16, const T1 f17,
                           const T1 f18, const T1 f19, const T1 f20,
                           const T1 f21, const T1 f22, const T1 f23,
                           const T1 f24, const std::shared_ptr<instr_acc> &i) {
    return std::visit(
        Overloaded{
            [&](const typename instr_acc::LDM _args) -> T1 {
              unsigned int n = _args.d_a0;
              return f(std::move(n));
            },
            [&](const typename instr_acc::LD _args) -> T1 {
              unsigned int n = _args.d_a0;
              return f0(std::move(n));
            },
            [&](const typename instr_acc::ADD _args) -> T1 {
              unsigned int n = _args.d_a0;
              return f1(std::move(n));
            },
            [&](const typename instr_acc::SUB _args) -> T1 {
              unsigned int n = _args.d_a0;
              return f2(std::move(n));
            },
            [&](const typename instr_acc::INC _args) -> T1 {
              unsigned int n = _args.d_a0;
              return f3(std::move(n));
            },
            [&](const typename instr_acc::XCH _args) -> T1 {
              unsigned int n = _args.d_a0;
              return f4(std::move(n));
            },
            [&](const typename instr_acc::BBL _args) -> T1 {
              unsigned int n = _args.d_a0;
              return f5(std::move(n));
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
            [&](const typename instr_acc::NOP_acc _args) -> T1 { return f24; }},
        i->v());
  }

  template <typename T1, MapsTo<T1, unsigned int> F0,
            MapsTo<T1, unsigned int> F1, MapsTo<T1, unsigned int> F2,
            MapsTo<T1, unsigned int> F3, MapsTo<T1, unsigned int> F4,
            MapsTo<T1, unsigned int> F5, MapsTo<T1, unsigned int> F6>
  static T1 instr_acc_rec(F0 &&f, F1 &&f0, F2 &&f1, F3 &&f2, F4 &&f3, F5 &&f4,
                          F6 &&f5, const T1 f6, const T1 f7, const T1 f8,
                          const T1 f9, const T1 f10, const T1 f11, const T1 f12,
                          const T1 f13, const T1 f14, const T1 f15,
                          const T1 f16, const T1 f17, const T1 f18,
                          const T1 f19, const T1 f20, const T1 f21,
                          const T1 f22, const T1 f23, const T1 f24,
                          const std::shared_ptr<instr_acc> &i) {
    return std::visit(
        Overloaded{
            [&](const typename instr_acc::LDM _args) -> T1 {
              unsigned int n = _args.d_a0;
              return f(std::move(n));
            },
            [&](const typename instr_acc::LD _args) -> T1 {
              unsigned int n = _args.d_a0;
              return f0(std::move(n));
            },
            [&](const typename instr_acc::ADD _args) -> T1 {
              unsigned int n = _args.d_a0;
              return f1(std::move(n));
            },
            [&](const typename instr_acc::SUB _args) -> T1 {
              unsigned int n = _args.d_a0;
              return f2(std::move(n));
            },
            [&](const typename instr_acc::INC _args) -> T1 {
              unsigned int n = _args.d_a0;
              return f3(std::move(n));
            },
            [&](const typename instr_acc::XCH _args) -> T1 {
              unsigned int n = _args.d_a0;
              return f4(std::move(n));
            },
            [&](const typename instr_acc::BBL _args) -> T1 {
              unsigned int n = _args.d_a0;
              return f5(std::move(n));
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
            [&](const typename instr_acc::NOP_acc _args) -> T1 { return f24; }},
        i->v());
  }

  __attribute__((pure)) static bool
  writes_acc(const std::shared_ptr<instr_acc> &i);
  __attribute__((pure)) static unsigned int count_writes_acc(
      const std::shared_ptr<List<std::shared_ptr<instr_acc>>> &prog);
  static inline const unsigned int test_writes_acc =
      count_writes_acc(List<std::shared_ptr<instr_acc>>::ctor::Cons_(
          instr_acc::ctor::NOP_acc_(),
          List<std::shared_ptr<instr_acc>>::ctor::Cons_(
              instr_acc::ctor::LDM_(9u),
              List<std::shared_ptr<instr_acc>>::ctor::Cons_(
                  instr_acc::ctor::RAR_(),
                  List<std::shared_ptr<instr_acc>>::ctor::Cons_(
                      instr_acc::ctor::KBP_(),
                      List<std::shared_ptr<instr_acc>>::ctor::Cons_(
                          instr_acc::ctor::NOP_acc_(),
                          List<std::shared_ptr<instr_acc>>::ctor::Cons_(
                              instr_acc::ctor::ADD_(1u),
                              List<std::shared_ptr<instr_acc>>::ctor::
                                  Nil_())))))));

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

    // CREATORS
    explicit instr_ram(WRM _v) : d_v_(std::move(_v)) {}

    explicit instr_ram(WMP _v) : d_v_(std::move(_v)) {}

    explicit instr_ram(WR0 _v) : d_v_(std::move(_v)) {}

    explicit instr_ram(WR1 _v) : d_v_(std::move(_v)) {}

    explicit instr_ram(WR2 _v) : d_v_(std::move(_v)) {}

    explicit instr_ram(WR3 _v) : d_v_(std::move(_v)) {}

    explicit instr_ram(NOP_ram _v) : d_v_(std::move(_v)) {}

    explicit instr_ram(ADD_ram _v) : d_v_(std::move(_v)) {}

  public:
    // TYPES
    struct ctor {
      ctor() = delete;

      static std::shared_ptr<instr_ram> WRM_() {
        return std::shared_ptr<instr_ram>(new instr_ram(WRM{}));
      }

      static std::shared_ptr<instr_ram> WMP_() {
        return std::shared_ptr<instr_ram>(new instr_ram(WMP{}));
      }

      static std::shared_ptr<instr_ram> WR0_() {
        return std::shared_ptr<instr_ram>(new instr_ram(WR0{}));
      }

      static std::shared_ptr<instr_ram> WR1_() {
        return std::shared_ptr<instr_ram>(new instr_ram(WR1{}));
      }

      static std::shared_ptr<instr_ram> WR2_() {
        return std::shared_ptr<instr_ram>(new instr_ram(WR2{}));
      }

      static std::shared_ptr<instr_ram> WR3_() {
        return std::shared_ptr<instr_ram>(new instr_ram(WR3{}));
      }

      static std::shared_ptr<instr_ram> NOP_ram_() {
        return std::shared_ptr<instr_ram>(new instr_ram(NOP_ram{}));
      }

      static std::shared_ptr<instr_ram> ADD_ram_(unsigned int a0) {
        return std::shared_ptr<instr_ram>(new instr_ram(ADD_ram{a0}));
      }

      static std::unique_ptr<instr_ram> WRM_uptr() {
        return std::unique_ptr<instr_ram>(new instr_ram(WRM{}));
      }

      static std::unique_ptr<instr_ram> WMP_uptr() {
        return std::unique_ptr<instr_ram>(new instr_ram(WMP{}));
      }

      static std::unique_ptr<instr_ram> WR0_uptr() {
        return std::unique_ptr<instr_ram>(new instr_ram(WR0{}));
      }

      static std::unique_ptr<instr_ram> WR1_uptr() {
        return std::unique_ptr<instr_ram>(new instr_ram(WR1{}));
      }

      static std::unique_ptr<instr_ram> WR2_uptr() {
        return std::unique_ptr<instr_ram>(new instr_ram(WR2{}));
      }

      static std::unique_ptr<instr_ram> WR3_uptr() {
        return std::unique_ptr<instr_ram>(new instr_ram(WR3{}));
      }

      static std::unique_ptr<instr_ram> NOP_ram_uptr() {
        return std::unique_ptr<instr_ram>(new instr_ram(NOP_ram{}));
      }

      static std::unique_ptr<instr_ram> ADD_ram_uptr(unsigned int a0) {
        return std::unique_ptr<instr_ram>(new instr_ram(ADD_ram{a0}));
      }
    };

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
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
              unsigned int n = _args.d_a0;
              return f6(std::move(n));
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
              unsigned int n = _args.d_a0;
              return f6(std::move(n));
            }},
        i->v());
  }

  __attribute__((pure)) static bool
  writes_ram(const std::shared_ptr<instr_ram> &i);
  __attribute__((pure)) static unsigned int count_writes_ram(
      const std::shared_ptr<List<std::shared_ptr<instr_ram>>> &prog);
  static inline const unsigned int test_writes_ram =
      count_writes_ram(List<std::shared_ptr<instr_ram>>::ctor::Cons_(
          instr_ram::ctor::NOP_ram_(),
          List<std::shared_ptr<instr_ram>>::ctor::Cons_(
              instr_ram::ctor::WRM_(),
              List<std::shared_ptr<instr_ram>>::ctor::Cons_(
                  instr_ram::ctor::ADD_ram_(3u),
                  List<std::shared_ptr<instr_ram>>::ctor::Cons_(
                      instr_ram::ctor::WR3_(),
                      List<std::shared_ptr<instr_ram>>::ctor::Cons_(
                          instr_ram::ctor::WMP_(),
                          List<std::shared_ptr<instr_ram>>::ctor::Cons_(
                              instr_ram::ctor::NOP_ram_(),
                              List<std::shared_ptr<instr_ram>>::ctor::
                                  Nil_())))))));

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

    // CREATORS
    explicit instr_regs(XCH_regs _v) : d_v_(std::move(_v)) {}

    explicit instr_regs(INC_regs _v) : d_v_(std::move(_v)) {}

    explicit instr_regs(FIM _v) : d_v_(std::move(_v)) {}

    explicit instr_regs(FIN _v) : d_v_(std::move(_v)) {}

    explicit instr_regs(ISZ _v) : d_v_(std::move(_v)) {}

    explicit instr_regs(NOP_regs _v) : d_v_(std::move(_v)) {}

    explicit instr_regs(ADD_regs _v) : d_v_(std::move(_v)) {}

  public:
    // TYPES
    struct ctor {
      ctor() = delete;

      static std::shared_ptr<instr_regs> XCH_regs_(unsigned int a0) {
        return std::shared_ptr<instr_regs>(new instr_regs(XCH_regs{a0}));
      }

      static std::shared_ptr<instr_regs> INC_regs_(unsigned int a0) {
        return std::shared_ptr<instr_regs>(new instr_regs(INC_regs{a0}));
      }

      static std::shared_ptr<instr_regs> FIM_(unsigned int a0,
                                              unsigned int a1) {
        return std::shared_ptr<instr_regs>(new instr_regs(FIM{a0, a1}));
      }

      static std::shared_ptr<instr_regs> FIN_(unsigned int a0) {
        return std::shared_ptr<instr_regs>(new instr_regs(FIN{a0}));
      }

      static std::shared_ptr<instr_regs> ISZ_(unsigned int a0,
                                              unsigned int a1) {
        return std::shared_ptr<instr_regs>(new instr_regs(ISZ{a0, a1}));
      }

      static std::shared_ptr<instr_regs> NOP_regs_() {
        return std::shared_ptr<instr_regs>(new instr_regs(NOP_regs{}));
      }

      static std::shared_ptr<instr_regs> ADD_regs_(unsigned int a0) {
        return std::shared_ptr<instr_regs>(new instr_regs(ADD_regs{a0}));
      }

      static std::unique_ptr<instr_regs> XCH_regs_uptr(unsigned int a0) {
        return std::unique_ptr<instr_regs>(new instr_regs(XCH_regs{a0}));
      }

      static std::unique_ptr<instr_regs> INC_regs_uptr(unsigned int a0) {
        return std::unique_ptr<instr_regs>(new instr_regs(INC_regs{a0}));
      }

      static std::unique_ptr<instr_regs> FIM_uptr(unsigned int a0,
                                                  unsigned int a1) {
        return std::unique_ptr<instr_regs>(new instr_regs(FIM{a0, a1}));
      }

      static std::unique_ptr<instr_regs> FIN_uptr(unsigned int a0) {
        return std::unique_ptr<instr_regs>(new instr_regs(FIN{a0}));
      }

      static std::unique_ptr<instr_regs> ISZ_uptr(unsigned int a0,
                                                  unsigned int a1) {
        return std::unique_ptr<instr_regs>(new instr_regs(ISZ{a0, a1}));
      }

      static std::unique_ptr<instr_regs> NOP_regs_uptr() {
        return std::unique_ptr<instr_regs>(new instr_regs(NOP_regs{}));
      }

      static std::unique_ptr<instr_regs> ADD_regs_uptr(unsigned int a0) {
        return std::unique_ptr<instr_regs>(new instr_regs(ADD_regs{a0}));
      }
    };

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <
      typename T1, MapsTo<T1, unsigned int> F0, MapsTo<T1, unsigned int> F1,
      MapsTo<T1, unsigned int, unsigned int> F2, MapsTo<T1, unsigned int> F3,
      MapsTo<T1, unsigned int, unsigned int> F4, MapsTo<T1, unsigned int> F6>
  static T1 instr_regs_rect(F0 &&f, F1 &&f0, F2 &&f1, F3 &&f2, F4 &&f3,
                            const T1 f4, F6 &&f5,
                            const std::shared_ptr<instr_regs> &i) {
    return std::visit(
        Overloaded{
            [&](const typename instr_regs::XCH_regs _args) -> T1 {
              unsigned int n = _args.d_a0;
              return f(std::move(n));
            },
            [&](const typename instr_regs::INC_regs _args) -> T1 {
              unsigned int n = _args.d_a0;
              return f0(std::move(n));
            },
            [&](const typename instr_regs::FIM _args) -> T1 {
              unsigned int n = _args.d_a0;
              unsigned int n0 = _args.d_a1;
              return f1(std::move(n), std::move(n0));
            },
            [&](const typename instr_regs::FIN _args) -> T1 {
              unsigned int n = _args.d_a0;
              return f2(std::move(n));
            },
            [&](const typename instr_regs::ISZ _args) -> T1 {
              unsigned int n = _args.d_a0;
              unsigned int n0 = _args.d_a1;
              return f3(std::move(n), std::move(n0));
            },
            [&](const typename instr_regs::NOP_regs _args) -> T1 { return f4; },
            [&](const typename instr_regs::ADD_regs _args) -> T1 {
              unsigned int n = _args.d_a0;
              return f5(std::move(n));
            }},
        i->v());
  }

  template <
      typename T1, MapsTo<T1, unsigned int> F0, MapsTo<T1, unsigned int> F1,
      MapsTo<T1, unsigned int, unsigned int> F2, MapsTo<T1, unsigned int> F3,
      MapsTo<T1, unsigned int, unsigned int> F4, MapsTo<T1, unsigned int> F6>
  static T1 instr_regs_rec(F0 &&f, F1 &&f0, F2 &&f1, F3 &&f2, F4 &&f3,
                           const T1 f4, F6 &&f5,
                           const std::shared_ptr<instr_regs> &i) {
    return std::visit(
        Overloaded{
            [&](const typename instr_regs::XCH_regs _args) -> T1 {
              unsigned int n = _args.d_a0;
              return f(std::move(n));
            },
            [&](const typename instr_regs::INC_regs _args) -> T1 {
              unsigned int n = _args.d_a0;
              return f0(std::move(n));
            },
            [&](const typename instr_regs::FIM _args) -> T1 {
              unsigned int n = _args.d_a0;
              unsigned int n0 = _args.d_a1;
              return f1(std::move(n), std::move(n0));
            },
            [&](const typename instr_regs::FIN _args) -> T1 {
              unsigned int n = _args.d_a0;
              return f2(std::move(n));
            },
            [&](const typename instr_regs::ISZ _args) -> T1 {
              unsigned int n = _args.d_a0;
              unsigned int n0 = _args.d_a1;
              return f3(std::move(n), std::move(n0));
            },
            [&](const typename instr_regs::NOP_regs _args) -> T1 { return f4; },
            [&](const typename instr_regs::ADD_regs _args) -> T1 {
              unsigned int n = _args.d_a0;
              return f5(std::move(n));
            }},
        i->v());
  }

  __attribute__((pure)) static bool
  writes_regs(const std::shared_ptr<instr_regs> &i);
  __attribute__((pure)) static unsigned int count_writes_regs(
      const std::shared_ptr<List<std::shared_ptr<instr_regs>>> &prog);
  static inline const unsigned int test_writes_regs =
      count_writes_regs(List<std::shared_ptr<instr_regs>>::ctor::Cons_(
          instr_regs::ctor::NOP_regs_(),
          List<std::shared_ptr<instr_regs>>::ctor::Cons_(
              instr_regs::ctor::FIM_(0u, 12u),
              List<std::shared_ptr<instr_regs>>::ctor::Cons_(
                  instr_regs::ctor::ADD_regs_(1u),
                  List<std::shared_ptr<instr_regs>>::ctor::Cons_(
                      instr_regs::ctor::INC_regs_(7u),
                      List<std::shared_ptr<instr_regs>>::ctor::Cons_(
                          instr_regs::ctor::ISZ_(1u, 2u),
                          List<std::shared_ptr<instr_regs>>::ctor::Nil_()))))));

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

    // CREATORS
    explicit instr_jump(JCN _v) : d_v_(std::move(_v)) {}

    explicit instr_jump(JUN _v) : d_v_(std::move(_v)) {}

    explicit instr_jump(JMS _v) : d_v_(std::move(_v)) {}

    explicit instr_jump(JIN _v) : d_v_(std::move(_v)) {}

    explicit instr_jump(BBL_jump _v) : d_v_(std::move(_v)) {}

    explicit instr_jump(ISZ_jump _v) : d_v_(std::move(_v)) {}

    explicit instr_jump(ADD_jump _v) : d_v_(std::move(_v)) {}

    explicit instr_jump(NOP_jump _v) : d_v_(std::move(_v)) {}

  public:
    // TYPES
    struct ctor {
      ctor() = delete;

      static std::shared_ptr<instr_jump> JCN_(unsigned int a0,
                                              unsigned int a1) {
        return std::shared_ptr<instr_jump>(new instr_jump(JCN{a0, a1}));
      }

      static std::shared_ptr<instr_jump> JUN_(unsigned int a0) {
        return std::shared_ptr<instr_jump>(new instr_jump(JUN{a0}));
      }

      static std::shared_ptr<instr_jump> JMS_(unsigned int a0) {
        return std::shared_ptr<instr_jump>(new instr_jump(JMS{a0}));
      }

      static std::shared_ptr<instr_jump> JIN_(unsigned int a0) {
        return std::shared_ptr<instr_jump>(new instr_jump(JIN{a0}));
      }

      static std::shared_ptr<instr_jump> BBL_jump_(unsigned int a0) {
        return std::shared_ptr<instr_jump>(new instr_jump(BBL_jump{a0}));
      }

      static std::shared_ptr<instr_jump> ISZ_jump_(unsigned int a0,
                                                   unsigned int a1) {
        return std::shared_ptr<instr_jump>(new instr_jump(ISZ_jump{a0, a1}));
      }

      static std::shared_ptr<instr_jump> ADD_jump_(unsigned int a0) {
        return std::shared_ptr<instr_jump>(new instr_jump(ADD_jump{a0}));
      }

      static std::shared_ptr<instr_jump> NOP_jump_() {
        return std::shared_ptr<instr_jump>(new instr_jump(NOP_jump{}));
      }

      static std::unique_ptr<instr_jump> JCN_uptr(unsigned int a0,
                                                  unsigned int a1) {
        return std::unique_ptr<instr_jump>(new instr_jump(JCN{a0, a1}));
      }

      static std::unique_ptr<instr_jump> JUN_uptr(unsigned int a0) {
        return std::unique_ptr<instr_jump>(new instr_jump(JUN{a0}));
      }

      static std::unique_ptr<instr_jump> JMS_uptr(unsigned int a0) {
        return std::unique_ptr<instr_jump>(new instr_jump(JMS{a0}));
      }

      static std::unique_ptr<instr_jump> JIN_uptr(unsigned int a0) {
        return std::unique_ptr<instr_jump>(new instr_jump(JIN{a0}));
      }

      static std::unique_ptr<instr_jump> BBL_jump_uptr(unsigned int a0) {
        return std::unique_ptr<instr_jump>(new instr_jump(BBL_jump{a0}));
      }

      static std::unique_ptr<instr_jump> ISZ_jump_uptr(unsigned int a0,
                                                       unsigned int a1) {
        return std::unique_ptr<instr_jump>(new instr_jump(ISZ_jump{a0, a1}));
      }

      static std::unique_ptr<instr_jump> ADD_jump_uptr(unsigned int a0) {
        return std::unique_ptr<instr_jump>(new instr_jump(ADD_jump{a0}));
      }

      static std::unique_ptr<instr_jump> NOP_jump_uptr() {
        return std::unique_ptr<instr_jump>(new instr_jump(NOP_jump{}));
      }
    };

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, MapsTo<T1, unsigned int, unsigned int> F0,
            MapsTo<T1, unsigned int> F1, MapsTo<T1, unsigned int> F2,
            MapsTo<T1, unsigned int> F3, MapsTo<T1, unsigned int> F4,
            MapsTo<T1, unsigned int, unsigned int> F5,
            MapsTo<T1, unsigned int> F6>
  static T1 instr_jump_rect(F0 &&f, F1 &&f0, F2 &&f1, F3 &&f2, F4 &&f3, F5 &&f4,
                            F6 &&f5, const T1 f6,
                            const std::shared_ptr<instr_jump> &i) {
    return std::visit(
        Overloaded{[&](const typename instr_jump::JCN _args) -> T1 {
                     unsigned int n = _args.d_a0;
                     unsigned int n0 = _args.d_a1;
                     return f(std::move(n), std::move(n0));
                   },
                   [&](const typename instr_jump::JUN _args) -> T1 {
                     unsigned int n = _args.d_a0;
                     return f0(std::move(n));
                   },
                   [&](const typename instr_jump::JMS _args) -> T1 {
                     unsigned int n = _args.d_a0;
                     return f1(std::move(n));
                   },
                   [&](const typename instr_jump::JIN _args) -> T1 {
                     unsigned int n = _args.d_a0;
                     return f2(std::move(n));
                   },
                   [&](const typename instr_jump::BBL_jump _args) -> T1 {
                     unsigned int n = _args.d_a0;
                     return f3(std::move(n));
                   },
                   [&](const typename instr_jump::ISZ_jump _args) -> T1 {
                     unsigned int n = _args.d_a0;
                     unsigned int n0 = _args.d_a1;
                     return f4(std::move(n), std::move(n0));
                   },
                   [&](const typename instr_jump::ADD_jump _args) -> T1 {
                     unsigned int n = _args.d_a0;
                     return f5(std::move(n));
                   },
                   [&](const typename instr_jump::NOP_jump _args) -> T1 {
                     return f6;
                   }},
        i->v());
  }

  template <typename T1, MapsTo<T1, unsigned int, unsigned int> F0,
            MapsTo<T1, unsigned int> F1, MapsTo<T1, unsigned int> F2,
            MapsTo<T1, unsigned int> F3, MapsTo<T1, unsigned int> F4,
            MapsTo<T1, unsigned int, unsigned int> F5,
            MapsTo<T1, unsigned int> F6>
  static T1 instr_jump_rec(F0 &&f, F1 &&f0, F2 &&f1, F3 &&f2, F4 &&f3, F5 &&f4,
                           F6 &&f5, const T1 f6,
                           const std::shared_ptr<instr_jump> &i) {
    return std::visit(
        Overloaded{[&](const typename instr_jump::JCN _args) -> T1 {
                     unsigned int n = _args.d_a0;
                     unsigned int n0 = _args.d_a1;
                     return f(std::move(n), std::move(n0));
                   },
                   [&](const typename instr_jump::JUN _args) -> T1 {
                     unsigned int n = _args.d_a0;
                     return f0(std::move(n));
                   },
                   [&](const typename instr_jump::JMS _args) -> T1 {
                     unsigned int n = _args.d_a0;
                     return f1(std::move(n));
                   },
                   [&](const typename instr_jump::JIN _args) -> T1 {
                     unsigned int n = _args.d_a0;
                     return f2(std::move(n));
                   },
                   [&](const typename instr_jump::BBL_jump _args) -> T1 {
                     unsigned int n = _args.d_a0;
                     return f3(std::move(n));
                   },
                   [&](const typename instr_jump::ISZ_jump _args) -> T1 {
                     unsigned int n = _args.d_a0;
                     unsigned int n0 = _args.d_a1;
                     return f4(std::move(n), std::move(n0));
                   },
                   [&](const typename instr_jump::ADD_jump _args) -> T1 {
                     unsigned int n = _args.d_a0;
                     return f5(std::move(n));
                   },
                   [&](const typename instr_jump::NOP_jump _args) -> T1 {
                     return f6;
                   }},
        i->v());
  }

  __attribute__((pure)) static bool
  is_jump(const std::shared_ptr<instr_jump> &i);
  __attribute__((pure)) static unsigned int
  count_jumps(const std::shared_ptr<List<std::shared_ptr<instr_jump>>> &prog);
  static inline const unsigned int test_jump_classifier =
      count_jumps(List<std::shared_ptr<instr_jump>>::ctor::Cons_(
          instr_jump::ctor::ADD_jump_(0u),
          List<std::shared_ptr<instr_jump>>::ctor::Cons_(
              instr_jump::ctor::JCN_(4u, 8u),
              List<std::shared_ptr<instr_jump>>::ctor::Cons_(
                  instr_jump::ctor::NOP_jump_(),
                  List<std::shared_ptr<instr_jump>>::ctor::Cons_(
                      instr_jump::ctor::JMS_(33u),
                      List<std::shared_ptr<instr_jump>>::ctor::Cons_(
                          instr_jump::ctor::ISZ_jump_(1u, 2u),
                          List<std::shared_ptr<instr_jump>>::ctor::Nil_()))))));
  static inline const std::pair<
      std::pair<std::pair<unsigned int, unsigned int>, unsigned int>,
      unsigned int>
      t = std::make_pair(
          std::make_pair(std::make_pair(test_writes_acc, test_writes_ram),
                         test_writes_regs),
          test_jump_classifier);
};

#endif // INCLUDED_INSTRUCTION_CLASSIFIERS
