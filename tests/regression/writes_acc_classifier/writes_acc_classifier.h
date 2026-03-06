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

template <typename A> struct List {
public:
  struct nil {};
  struct cons {
    A _a0;
    std::shared_ptr<List<A>> _a1;
  };
  using variant_t = std::variant<nil, cons>;

private:
  variant_t v_;
  explicit List(nil _v) : v_(std::move(_v)) {}
  explicit List(cons _v) : v_(std::move(_v)) {}

public:
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
  const variant_t &v() const { return v_; }
  variant_t &v_mut() { return v_; }
};

struct WritesAccClassifier {
  struct instruction {
  public:
    struct LDM {
      unsigned int _a0;
    };
    struct LD {
      unsigned int _a0;
    };
    struct ADD {
      unsigned int _a0;
    };
    struct SUB {
      unsigned int _a0;
    };
    struct INC {
      unsigned int _a0;
    };
    struct XCH {
      unsigned int _a0;
    };
    struct BBL {
      unsigned int _a0;
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
    struct NOP {};
    using variant_t = std::variant<LDM, LD, ADD, SUB, INC, XCH, BBL, SBM, RDM,
                                   RDR, ADM, RD0, RD1, RD2, RD3, CLB, CMA, IAC,
                                   DAC, RAL, RAR, TCC, TCS, DAA, KBP, NOP>;

  private:
    variant_t v_;
    explicit instruction(LDM _v) : v_(std::move(_v)) {}
    explicit instruction(LD _v) : v_(std::move(_v)) {}
    explicit instruction(ADD _v) : v_(std::move(_v)) {}
    explicit instruction(SUB _v) : v_(std::move(_v)) {}
    explicit instruction(INC _v) : v_(std::move(_v)) {}
    explicit instruction(XCH _v) : v_(std::move(_v)) {}
    explicit instruction(BBL _v) : v_(std::move(_v)) {}
    explicit instruction(SBM _v) : v_(std::move(_v)) {}
    explicit instruction(RDM _v) : v_(std::move(_v)) {}
    explicit instruction(RDR _v) : v_(std::move(_v)) {}
    explicit instruction(ADM _v) : v_(std::move(_v)) {}
    explicit instruction(RD0 _v) : v_(std::move(_v)) {}
    explicit instruction(RD1 _v) : v_(std::move(_v)) {}
    explicit instruction(RD2 _v) : v_(std::move(_v)) {}
    explicit instruction(RD3 _v) : v_(std::move(_v)) {}
    explicit instruction(CLB _v) : v_(std::move(_v)) {}
    explicit instruction(CMA _v) : v_(std::move(_v)) {}
    explicit instruction(IAC _v) : v_(std::move(_v)) {}
    explicit instruction(DAC _v) : v_(std::move(_v)) {}
    explicit instruction(RAL _v) : v_(std::move(_v)) {}
    explicit instruction(RAR _v) : v_(std::move(_v)) {}
    explicit instruction(TCC _v) : v_(std::move(_v)) {}
    explicit instruction(TCS _v) : v_(std::move(_v)) {}
    explicit instruction(DAA _v) : v_(std::move(_v)) {}
    explicit instruction(KBP _v) : v_(std::move(_v)) {}
    explicit instruction(NOP _v) : v_(std::move(_v)) {}

  public:
    struct ctor {
      ctor() = delete;
      static std::shared_ptr<instruction> LDM_(unsigned int a0) {
        return std::shared_ptr<instruction>(new instruction(LDM{a0}));
      }
      static std::shared_ptr<instruction> LD_(unsigned int a0) {
        return std::shared_ptr<instruction>(new instruction(LD{a0}));
      }
      static std::shared_ptr<instruction> ADD_(unsigned int a0) {
        return std::shared_ptr<instruction>(new instruction(ADD{a0}));
      }
      static std::shared_ptr<instruction> SUB_(unsigned int a0) {
        return std::shared_ptr<instruction>(new instruction(SUB{a0}));
      }
      static std::shared_ptr<instruction> INC_(unsigned int a0) {
        return std::shared_ptr<instruction>(new instruction(INC{a0}));
      }
      static std::shared_ptr<instruction> XCH_(unsigned int a0) {
        return std::shared_ptr<instruction>(new instruction(XCH{a0}));
      }
      static std::shared_ptr<instruction> BBL_(unsigned int a0) {
        return std::shared_ptr<instruction>(new instruction(BBL{a0}));
      }
      static std::shared_ptr<instruction> SBM_() {
        return std::shared_ptr<instruction>(new instruction(SBM{}));
      }
      static std::shared_ptr<instruction> RDM_() {
        return std::shared_ptr<instruction>(new instruction(RDM{}));
      }
      static std::shared_ptr<instruction> RDR_() {
        return std::shared_ptr<instruction>(new instruction(RDR{}));
      }
      static std::shared_ptr<instruction> ADM_() {
        return std::shared_ptr<instruction>(new instruction(ADM{}));
      }
      static std::shared_ptr<instruction> RD0_() {
        return std::shared_ptr<instruction>(new instruction(RD0{}));
      }
      static std::shared_ptr<instruction> RD1_() {
        return std::shared_ptr<instruction>(new instruction(RD1{}));
      }
      static std::shared_ptr<instruction> RD2_() {
        return std::shared_ptr<instruction>(new instruction(RD2{}));
      }
      static std::shared_ptr<instruction> RD3_() {
        return std::shared_ptr<instruction>(new instruction(RD3{}));
      }
      static std::shared_ptr<instruction> CLB_() {
        return std::shared_ptr<instruction>(new instruction(CLB{}));
      }
      static std::shared_ptr<instruction> CMA_() {
        return std::shared_ptr<instruction>(new instruction(CMA{}));
      }
      static std::shared_ptr<instruction> IAC_() {
        return std::shared_ptr<instruction>(new instruction(IAC{}));
      }
      static std::shared_ptr<instruction> DAC_() {
        return std::shared_ptr<instruction>(new instruction(DAC{}));
      }
      static std::shared_ptr<instruction> RAL_() {
        return std::shared_ptr<instruction>(new instruction(RAL{}));
      }
      static std::shared_ptr<instruction> RAR_() {
        return std::shared_ptr<instruction>(new instruction(RAR{}));
      }
      static std::shared_ptr<instruction> TCC_() {
        return std::shared_ptr<instruction>(new instruction(TCC{}));
      }
      static std::shared_ptr<instruction> TCS_() {
        return std::shared_ptr<instruction>(new instruction(TCS{}));
      }
      static std::shared_ptr<instruction> DAA_() {
        return std::shared_ptr<instruction>(new instruction(DAA{}));
      }
      static std::shared_ptr<instruction> KBP_() {
        return std::shared_ptr<instruction>(new instruction(KBP{}));
      }
      static std::shared_ptr<instruction> NOP_() {
        return std::shared_ptr<instruction>(new instruction(NOP{}));
      }
      static std::unique_ptr<instruction> LDM_uptr(unsigned int a0) {
        return std::unique_ptr<instruction>(new instruction(LDM{a0}));
      }
      static std::unique_ptr<instruction> LD_uptr(unsigned int a0) {
        return std::unique_ptr<instruction>(new instruction(LD{a0}));
      }
      static std::unique_ptr<instruction> ADD_uptr(unsigned int a0) {
        return std::unique_ptr<instruction>(new instruction(ADD{a0}));
      }
      static std::unique_ptr<instruction> SUB_uptr(unsigned int a0) {
        return std::unique_ptr<instruction>(new instruction(SUB{a0}));
      }
      static std::unique_ptr<instruction> INC_uptr(unsigned int a0) {
        return std::unique_ptr<instruction>(new instruction(INC{a0}));
      }
      static std::unique_ptr<instruction> XCH_uptr(unsigned int a0) {
        return std::unique_ptr<instruction>(new instruction(XCH{a0}));
      }
      static std::unique_ptr<instruction> BBL_uptr(unsigned int a0) {
        return std::unique_ptr<instruction>(new instruction(BBL{a0}));
      }
      static std::unique_ptr<instruction> SBM_uptr() {
        return std::unique_ptr<instruction>(new instruction(SBM{}));
      }
      static std::unique_ptr<instruction> RDM_uptr() {
        return std::unique_ptr<instruction>(new instruction(RDM{}));
      }
      static std::unique_ptr<instruction> RDR_uptr() {
        return std::unique_ptr<instruction>(new instruction(RDR{}));
      }
      static std::unique_ptr<instruction> ADM_uptr() {
        return std::unique_ptr<instruction>(new instruction(ADM{}));
      }
      static std::unique_ptr<instruction> RD0_uptr() {
        return std::unique_ptr<instruction>(new instruction(RD0{}));
      }
      static std::unique_ptr<instruction> RD1_uptr() {
        return std::unique_ptr<instruction>(new instruction(RD1{}));
      }
      static std::unique_ptr<instruction> RD2_uptr() {
        return std::unique_ptr<instruction>(new instruction(RD2{}));
      }
      static std::unique_ptr<instruction> RD3_uptr() {
        return std::unique_ptr<instruction>(new instruction(RD3{}));
      }
      static std::unique_ptr<instruction> CLB_uptr() {
        return std::unique_ptr<instruction>(new instruction(CLB{}));
      }
      static std::unique_ptr<instruction> CMA_uptr() {
        return std::unique_ptr<instruction>(new instruction(CMA{}));
      }
      static std::unique_ptr<instruction> IAC_uptr() {
        return std::unique_ptr<instruction>(new instruction(IAC{}));
      }
      static std::unique_ptr<instruction> DAC_uptr() {
        return std::unique_ptr<instruction>(new instruction(DAC{}));
      }
      static std::unique_ptr<instruction> RAL_uptr() {
        return std::unique_ptr<instruction>(new instruction(RAL{}));
      }
      static std::unique_ptr<instruction> RAR_uptr() {
        return std::unique_ptr<instruction>(new instruction(RAR{}));
      }
      static std::unique_ptr<instruction> TCC_uptr() {
        return std::unique_ptr<instruction>(new instruction(TCC{}));
      }
      static std::unique_ptr<instruction> TCS_uptr() {
        return std::unique_ptr<instruction>(new instruction(TCS{}));
      }
      static std::unique_ptr<instruction> DAA_uptr() {
        return std::unique_ptr<instruction>(new instruction(DAA{}));
      }
      static std::unique_ptr<instruction> KBP_uptr() {
        return std::unique_ptr<instruction>(new instruction(KBP{}));
      }
      static std::unique_ptr<instruction> NOP_uptr() {
        return std::unique_ptr<instruction>(new instruction(NOP{}));
      }
    };
    const variant_t &v() const { return v_; }
    variant_t &v_mut() { return v_; }
  };

  template <typename T1, MapsTo<T1, unsigned int> F0,
            MapsTo<T1, unsigned int> F1, MapsTo<T1, unsigned int> F2,
            MapsTo<T1, unsigned int> F3, MapsTo<T1, unsigned int> F4,
            MapsTo<T1, unsigned int> F5, MapsTo<T1, unsigned int> F6>
  static T1
  instruction_rect(F0 &&f, F1 &&f0, F2 &&f1, F3 &&f2, F4 &&f3, F5 &&f4, F6 &&f5,
                   const T1 f6, const T1 f7, const T1 f8, const T1 f9,
                   const T1 f10, const T1 f11, const T1 f12, const T1 f13,
                   const T1 f14, const T1 f15, const T1 f16, const T1 f17,
                   const T1 f18, const T1 f19, const T1 f20, const T1 f21,
                   const T1 f22, const T1 f23, const T1 f24,
                   const std::shared_ptr<instruction> &i) {
    return std::visit(
        Overloaded{
            [&](const typename instruction::LDM _args) -> T1 {
              unsigned int n = _args._a0;
              return f(std::move(n));
            },
            [&](const typename instruction::LD _args) -> T1 {
              unsigned int n = _args._a0;
              return f0(std::move(n));
            },
            [&](const typename instruction::ADD _args) -> T1 {
              unsigned int n = _args._a0;
              return f1(std::move(n));
            },
            [&](const typename instruction::SUB _args) -> T1 {
              unsigned int n = _args._a0;
              return f2(std::move(n));
            },
            [&](const typename instruction::INC _args) -> T1 {
              unsigned int n = _args._a0;
              return f3(std::move(n));
            },
            [&](const typename instruction::XCH _args) -> T1 {
              unsigned int n = _args._a0;
              return f4(std::move(n));
            },
            [&](const typename instruction::BBL _args) -> T1 {
              unsigned int n = _args._a0;
              return f5(std::move(n));
            },
            [&](const typename instruction::SBM _args) -> T1 { return f6; },
            [&](const typename instruction::RDM _args) -> T1 { return f7; },
            [&](const typename instruction::RDR _args) -> T1 { return f8; },
            [&](const typename instruction::ADM _args) -> T1 { return f9; },
            [&](const typename instruction::RD0 _args) -> T1 { return f10; },
            [&](const typename instruction::RD1 _args) -> T1 { return f11; },
            [&](const typename instruction::RD2 _args) -> T1 { return f12; },
            [&](const typename instruction::RD3 _args) -> T1 { return f13; },
            [&](const typename instruction::CLB _args) -> T1 { return f14; },
            [&](const typename instruction::CMA _args) -> T1 { return f15; },
            [&](const typename instruction::IAC _args) -> T1 { return f16; },
            [&](const typename instruction::DAC _args) -> T1 { return f17; },
            [&](const typename instruction::RAL _args) -> T1 { return f18; },
            [&](const typename instruction::RAR _args) -> T1 { return f19; },
            [&](const typename instruction::TCC _args) -> T1 { return f20; },
            [&](const typename instruction::TCS _args) -> T1 { return f21; },
            [&](const typename instruction::DAA _args) -> T1 { return f22; },
            [&](const typename instruction::KBP _args) -> T1 { return f23; },
            [&](const typename instruction::NOP _args) -> T1 { return f24; }},
        i->v());
  }

  template <typename T1, MapsTo<T1, unsigned int> F0,
            MapsTo<T1, unsigned int> F1, MapsTo<T1, unsigned int> F2,
            MapsTo<T1, unsigned int> F3, MapsTo<T1, unsigned int> F4,
            MapsTo<T1, unsigned int> F5, MapsTo<T1, unsigned int> F6>
  static T1
  instruction_rec(F0 &&f, F1 &&f0, F2 &&f1, F3 &&f2, F4 &&f3, F5 &&f4, F6 &&f5,
                  const T1 f6, const T1 f7, const T1 f8, const T1 f9,
                  const T1 f10, const T1 f11, const T1 f12, const T1 f13,
                  const T1 f14, const T1 f15, const T1 f16, const T1 f17,
                  const T1 f18, const T1 f19, const T1 f20, const T1 f21,
                  const T1 f22, const T1 f23, const T1 f24,
                  const std::shared_ptr<instruction> &i) {
    return std::visit(
        Overloaded{
            [&](const typename instruction::LDM _args) -> T1 {
              unsigned int n = _args._a0;
              return f(std::move(n));
            },
            [&](const typename instruction::LD _args) -> T1 {
              unsigned int n = _args._a0;
              return f0(std::move(n));
            },
            [&](const typename instruction::ADD _args) -> T1 {
              unsigned int n = _args._a0;
              return f1(std::move(n));
            },
            [&](const typename instruction::SUB _args) -> T1 {
              unsigned int n = _args._a0;
              return f2(std::move(n));
            },
            [&](const typename instruction::INC _args) -> T1 {
              unsigned int n = _args._a0;
              return f3(std::move(n));
            },
            [&](const typename instruction::XCH _args) -> T1 {
              unsigned int n = _args._a0;
              return f4(std::move(n));
            },
            [&](const typename instruction::BBL _args) -> T1 {
              unsigned int n = _args._a0;
              return f5(std::move(n));
            },
            [&](const typename instruction::SBM _args) -> T1 { return f6; },
            [&](const typename instruction::RDM _args) -> T1 { return f7; },
            [&](const typename instruction::RDR _args) -> T1 { return f8; },
            [&](const typename instruction::ADM _args) -> T1 { return f9; },
            [&](const typename instruction::RD0 _args) -> T1 { return f10; },
            [&](const typename instruction::RD1 _args) -> T1 { return f11; },
            [&](const typename instruction::RD2 _args) -> T1 { return f12; },
            [&](const typename instruction::RD3 _args) -> T1 { return f13; },
            [&](const typename instruction::CLB _args) -> T1 { return f14; },
            [&](const typename instruction::CMA _args) -> T1 { return f15; },
            [&](const typename instruction::IAC _args) -> T1 { return f16; },
            [&](const typename instruction::DAC _args) -> T1 { return f17; },
            [&](const typename instruction::RAL _args) -> T1 { return f18; },
            [&](const typename instruction::RAR _args) -> T1 { return f19; },
            [&](const typename instruction::TCC _args) -> T1 { return f20; },
            [&](const typename instruction::TCS _args) -> T1 { return f21; },
            [&](const typename instruction::DAA _args) -> T1 { return f22; },
            [&](const typename instruction::KBP _args) -> T1 { return f23; },
            [&](const typename instruction::NOP _args) -> T1 { return f24; }},
        i->v());
  }

  static bool writes_acc(const std::shared_ptr<instruction> &i);

  static unsigned int count_writes_acc(
      const std::shared_ptr<List<std::shared_ptr<instruction>>> &prog);

  static inline const unsigned int t =
      count_writes_acc(List<std::shared_ptr<instruction>>::ctor::cons_(
          instruction::ctor::NOP_(),
          List<std::shared_ptr<instruction>>::ctor::cons_(
              instruction::ctor::LDM_(
                  (((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1)),
              List<std::shared_ptr<instruction>>::ctor::cons_(
                  instruction::ctor::RAR_(),
                  List<std::shared_ptr<instruction>>::ctor::cons_(
                      instruction::ctor::KBP_(),
                      List<std::shared_ptr<instruction>>::ctor::cons_(
                          instruction::ctor::NOP_(),
                          List<std::shared_ptr<instruction>>::ctor::cons_(
                              instruction::ctor::ADD_((0 + 1)),
                              List<std::shared_ptr<instruction>>::ctor::
                                  nil_())))))));
};
