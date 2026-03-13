#ifndef INCLUDED_GET_PAIR_BOUND_PROP
#define INCLUDED_GET_PAIR_BOUND_PROP

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

template <typename t_A>
struct List : public std::enable_shared_from_this<List<t_A>> {
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

  std::shared_ptr<List<t_A>> skipn(const unsigned int n) const {
    if (n <= 0) {
      return std::const_pointer_cast<List<t_A>>(this->shared_from_this());
    } else {
      unsigned int n0 = n - 1;
      return std::visit(Overloaded{[](const typename List<t_A>::Nil _args)
                                       -> std::shared_ptr<List<t_A>> {
                                     return List<t_A>::ctor::Nil_();
                                   },
                                   [&](const typename List<t_A>::Cons _args)
                                       -> std::shared_ptr<List<t_A>> {
                                     std::shared_ptr<List<t_A>> l0 = _args.d_a1;
                                     return std::move(l0)->skipn(n0);
                                   }},
                        this->v());
    }
  }

  std::shared_ptr<List<t_A>> firstn(const unsigned int n) const {
    if (n <= 0) {
      return List<t_A>::ctor::Nil_();
    } else {
      unsigned int n0 = n - 1;
      return std::visit(Overloaded{[](const typename List<t_A>::Nil _args)
                                       -> std::shared_ptr<List<t_A>> {
                                     return List<t_A>::ctor::Nil_();
                                   },
                                   [&](const typename List<t_A>::Cons _args)
                                       -> std::shared_ptr<List<t_A>> {
                                     t_A a = _args.d_a0;
                                     std::shared_ptr<List<t_A>> l0 = _args.d_a1;
                                     return List<t_A>::ctor::Cons_(
                                         a, std::move(l0)->firstn(n0));
                                   }},
                        this->v());
    }
  }

  t_A nth(const unsigned int n, const t_A default0) const {
    if (n <= 0) {
      return std::visit(
          Overloaded{[&](const typename List<t_A>::Nil _args) -> t_A {
                       return default0;
                     },
                     [](const typename List<t_A>::Cons _args) -> t_A {
                       t_A x = _args.d_a0;
                       return x;
                     }},
          this->v());
    } else {
      unsigned int m = n - 1;
      return std::visit(
          Overloaded{[&](const typename List<t_A>::Nil _args) -> t_A {
                       return default0;
                     },
                     [&](const typename List<t_A>::Cons _args) -> t_A {
                       std::shared_ptr<List<t_A>> l_ = _args.d_a1;
                       return std::move(l_)->nth(m, default0);
                     }},
          this->v());
    }
  }
};

struct Nat {
  __attribute__((pure)) static std::pair<unsigned int, unsigned int>
  divmod(const unsigned int x, const unsigned int y, const unsigned int q,
         const unsigned int u);
  __attribute__((pure)) static unsigned int div(const unsigned int x,
                                                const unsigned int y);
};

struct GetPairBoundProp {
  template <typename T1>
  static std::shared_ptr<List<T1>>
  update_nth(const unsigned int n, const T1 x,
             const std::shared_ptr<List<T1>> &l) {
    if (n <= 0) {
      return std::visit(Overloaded{[](const typename List<T1>::Nil _args)
                                       -> std::shared_ptr<List<T1>> {
                                     return List<T1>::ctor::Nil_();
                                   },
                                   [&](const typename List<T1>::Cons _args)
                                       -> std::shared_ptr<List<T1>> {
                                     std::shared_ptr<List<T1>> xs = _args.d_a1;
                                     return List<T1>::ctor::Cons_(
                                         x, std::move(xs));
                                   }},
                        l->v());
    } else {
      unsigned int n_ = n - 1;
      return std::visit(Overloaded{[](const typename List<T1>::Nil _args)
                                       -> std::shared_ptr<List<T1>> {
                                     return List<T1>::ctor::Nil_();
                                   },
                                   [&](const typename List<T1>::Cons _args)
                                       -> std::shared_ptr<List<T1>> {
                                     T1 y = _args.d_a0;
                                     std::shared_ptr<List<T1>> ys = _args.d_a1;
                                     return List<T1>::ctor::Cons_(
                                         y,
                                         update_nth<T1>(n_, x, std::move(ys)));
                                   }},
                        l->v());
    }
  }

  struct state {
    unsigned int ex_acc;
    std::shared_ptr<List<unsigned int>> ex_regs;
    bool ex_carry;
    unsigned int ex_pc;
    std::shared_ptr<List<unsigned int>> ex_stack;
    unsigned int ex_pair_bus;
    std::shared_ptr<List<unsigned int>> ex_ports;
  };

  __attribute__((pure)) static unsigned int
  get_reg(const std::shared_ptr<state> &s, const unsigned int r);
  static std::shared_ptr<List<unsigned int>>
  set_reg(const std::shared_ptr<state> &s, const unsigned int r,
          const unsigned int v);
  __attribute__((pure)) static unsigned int pair_base(const unsigned int r);
  __attribute__((pure)) static unsigned int
  get_pair(const std::shared_ptr<state> &s, const unsigned int r);
  static std::shared_ptr<List<unsigned int>>
  set_pair(const std::shared_ptr<state> &s, const unsigned int r,
           const unsigned int v);
  static std::shared_ptr<List<unsigned int>>
  push_return(std::shared_ptr<state> s, const unsigned int ret);

  struct instr {
    // TYPES
    struct NOP {};

    struct LDM {
      unsigned int d_a0;
    };

    struct LD {
      unsigned int d_a0;
    };

    struct XCH {
      unsigned int d_a0;
    };

    struct INC {
      unsigned int d_a0;
    };

    struct ADD {
      unsigned int d_a0;
    };

    struct SUB {
      unsigned int d_a0;
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
      unsigned int d_a0;
    };

    struct JMS {
      unsigned int d_a0;
    };

    struct JCN {
      unsigned int d_a0;
      unsigned int d_a1;
    };

    struct FIM {
      unsigned int d_a0;
      unsigned int d_a1;
    };

    struct SRC {
      unsigned int d_a0;
    };

    struct FIN {
      unsigned int d_a0;
    };

    struct JIN {
      unsigned int d_a0;
    };

    struct ISZ {
      unsigned int d_a0;
      unsigned int d_a1;
    };

    struct BBL {
      unsigned int d_a0;
    };

    using variant_t =
        std::variant<NOP, LDM, LD, XCH, INC, ADD, SUB, IAC, DAC, CLC, STC, CMC,
                     CMA, CLB, RAL, RAR, TCC, TCS, DAA, KBP, JUN, JMS, JCN, FIM,
                     SRC, FIN, JIN, ISZ, BBL>;

  private:
    // DATA
    variant_t d_v_;

    // CREATORS
    explicit instr(NOP _v) : d_v_(std::move(_v)) {}

    explicit instr(LDM _v) : d_v_(std::move(_v)) {}

    explicit instr(LD _v) : d_v_(std::move(_v)) {}

    explicit instr(XCH _v) : d_v_(std::move(_v)) {}

    explicit instr(INC _v) : d_v_(std::move(_v)) {}

    explicit instr(ADD _v) : d_v_(std::move(_v)) {}

    explicit instr(SUB _v) : d_v_(std::move(_v)) {}

    explicit instr(IAC _v) : d_v_(std::move(_v)) {}

    explicit instr(DAC _v) : d_v_(std::move(_v)) {}

    explicit instr(CLC _v) : d_v_(std::move(_v)) {}

    explicit instr(STC _v) : d_v_(std::move(_v)) {}

    explicit instr(CMC _v) : d_v_(std::move(_v)) {}

    explicit instr(CMA _v) : d_v_(std::move(_v)) {}

    explicit instr(CLB _v) : d_v_(std::move(_v)) {}

    explicit instr(RAL _v) : d_v_(std::move(_v)) {}

    explicit instr(RAR _v) : d_v_(std::move(_v)) {}

    explicit instr(TCC _v) : d_v_(std::move(_v)) {}

    explicit instr(TCS _v) : d_v_(std::move(_v)) {}

    explicit instr(DAA _v) : d_v_(std::move(_v)) {}

    explicit instr(KBP _v) : d_v_(std::move(_v)) {}

    explicit instr(JUN _v) : d_v_(std::move(_v)) {}

    explicit instr(JMS _v) : d_v_(std::move(_v)) {}

    explicit instr(JCN _v) : d_v_(std::move(_v)) {}

    explicit instr(FIM _v) : d_v_(std::move(_v)) {}

    explicit instr(SRC _v) : d_v_(std::move(_v)) {}

    explicit instr(FIN _v) : d_v_(std::move(_v)) {}

    explicit instr(JIN _v) : d_v_(std::move(_v)) {}

    explicit instr(ISZ _v) : d_v_(std::move(_v)) {}

    explicit instr(BBL _v) : d_v_(std::move(_v)) {}

  public:
    // TYPES
    struct ctor {
      ctor() = delete;

      static std::shared_ptr<instr> NOP_() {
        return std::shared_ptr<instr>(new instr(NOP{}));
      }

      static std::shared_ptr<instr> LDM_(unsigned int a0) {
        return std::shared_ptr<instr>(new instr(LDM{a0}));
      }

      static std::shared_ptr<instr> LD_(unsigned int a0) {
        return std::shared_ptr<instr>(new instr(LD{a0}));
      }

      static std::shared_ptr<instr> XCH_(unsigned int a0) {
        return std::shared_ptr<instr>(new instr(XCH{a0}));
      }

      static std::shared_ptr<instr> INC_(unsigned int a0) {
        return std::shared_ptr<instr>(new instr(INC{a0}));
      }

      static std::shared_ptr<instr> ADD_(unsigned int a0) {
        return std::shared_ptr<instr>(new instr(ADD{a0}));
      }

      static std::shared_ptr<instr> SUB_(unsigned int a0) {
        return std::shared_ptr<instr>(new instr(SUB{a0}));
      }

      static std::shared_ptr<instr> IAC_() {
        return std::shared_ptr<instr>(new instr(IAC{}));
      }

      static std::shared_ptr<instr> DAC_() {
        return std::shared_ptr<instr>(new instr(DAC{}));
      }

      static std::shared_ptr<instr> CLC_() {
        return std::shared_ptr<instr>(new instr(CLC{}));
      }

      static std::shared_ptr<instr> STC_() {
        return std::shared_ptr<instr>(new instr(STC{}));
      }

      static std::shared_ptr<instr> CMC_() {
        return std::shared_ptr<instr>(new instr(CMC{}));
      }

      static std::shared_ptr<instr> CMA_() {
        return std::shared_ptr<instr>(new instr(CMA{}));
      }

      static std::shared_ptr<instr> CLB_() {
        return std::shared_ptr<instr>(new instr(CLB{}));
      }

      static std::shared_ptr<instr> RAL_() {
        return std::shared_ptr<instr>(new instr(RAL{}));
      }

      static std::shared_ptr<instr> RAR_() {
        return std::shared_ptr<instr>(new instr(RAR{}));
      }

      static std::shared_ptr<instr> TCC_() {
        return std::shared_ptr<instr>(new instr(TCC{}));
      }

      static std::shared_ptr<instr> TCS_() {
        return std::shared_ptr<instr>(new instr(TCS{}));
      }

      static std::shared_ptr<instr> DAA_() {
        return std::shared_ptr<instr>(new instr(DAA{}));
      }

      static std::shared_ptr<instr> KBP_() {
        return std::shared_ptr<instr>(new instr(KBP{}));
      }

      static std::shared_ptr<instr> JUN_(unsigned int a0) {
        return std::shared_ptr<instr>(new instr(JUN{a0}));
      }

      static std::shared_ptr<instr> JMS_(unsigned int a0) {
        return std::shared_ptr<instr>(new instr(JMS{a0}));
      }

      static std::shared_ptr<instr> JCN_(unsigned int a0, unsigned int a1) {
        return std::shared_ptr<instr>(new instr(JCN{a0, a1}));
      }

      static std::shared_ptr<instr> FIM_(unsigned int a0, unsigned int a1) {
        return std::shared_ptr<instr>(new instr(FIM{a0, a1}));
      }

      static std::shared_ptr<instr> SRC_(unsigned int a0) {
        return std::shared_ptr<instr>(new instr(SRC{a0}));
      }

      static std::shared_ptr<instr> FIN_(unsigned int a0) {
        return std::shared_ptr<instr>(new instr(FIN{a0}));
      }

      static std::shared_ptr<instr> JIN_(unsigned int a0) {
        return std::shared_ptr<instr>(new instr(JIN{a0}));
      }

      static std::shared_ptr<instr> ISZ_(unsigned int a0, unsigned int a1) {
        return std::shared_ptr<instr>(new instr(ISZ{a0, a1}));
      }

      static std::shared_ptr<instr> BBL_(unsigned int a0) {
        return std::shared_ptr<instr>(new instr(BBL{a0}));
      }

      static std::unique_ptr<instr> NOP_uptr() {
        return std::unique_ptr<instr>(new instr(NOP{}));
      }

      static std::unique_ptr<instr> LDM_uptr(unsigned int a0) {
        return std::unique_ptr<instr>(new instr(LDM{a0}));
      }

      static std::unique_ptr<instr> LD_uptr(unsigned int a0) {
        return std::unique_ptr<instr>(new instr(LD{a0}));
      }

      static std::unique_ptr<instr> XCH_uptr(unsigned int a0) {
        return std::unique_ptr<instr>(new instr(XCH{a0}));
      }

      static std::unique_ptr<instr> INC_uptr(unsigned int a0) {
        return std::unique_ptr<instr>(new instr(INC{a0}));
      }

      static std::unique_ptr<instr> ADD_uptr(unsigned int a0) {
        return std::unique_ptr<instr>(new instr(ADD{a0}));
      }

      static std::unique_ptr<instr> SUB_uptr(unsigned int a0) {
        return std::unique_ptr<instr>(new instr(SUB{a0}));
      }

      static std::unique_ptr<instr> IAC_uptr() {
        return std::unique_ptr<instr>(new instr(IAC{}));
      }

      static std::unique_ptr<instr> DAC_uptr() {
        return std::unique_ptr<instr>(new instr(DAC{}));
      }

      static std::unique_ptr<instr> CLC_uptr() {
        return std::unique_ptr<instr>(new instr(CLC{}));
      }

      static std::unique_ptr<instr> STC_uptr() {
        return std::unique_ptr<instr>(new instr(STC{}));
      }

      static std::unique_ptr<instr> CMC_uptr() {
        return std::unique_ptr<instr>(new instr(CMC{}));
      }

      static std::unique_ptr<instr> CMA_uptr() {
        return std::unique_ptr<instr>(new instr(CMA{}));
      }

      static std::unique_ptr<instr> CLB_uptr() {
        return std::unique_ptr<instr>(new instr(CLB{}));
      }

      static std::unique_ptr<instr> RAL_uptr() {
        return std::unique_ptr<instr>(new instr(RAL{}));
      }

      static std::unique_ptr<instr> RAR_uptr() {
        return std::unique_ptr<instr>(new instr(RAR{}));
      }

      static std::unique_ptr<instr> TCC_uptr() {
        return std::unique_ptr<instr>(new instr(TCC{}));
      }

      static std::unique_ptr<instr> TCS_uptr() {
        return std::unique_ptr<instr>(new instr(TCS{}));
      }

      static std::unique_ptr<instr> DAA_uptr() {
        return std::unique_ptr<instr>(new instr(DAA{}));
      }

      static std::unique_ptr<instr> KBP_uptr() {
        return std::unique_ptr<instr>(new instr(KBP{}));
      }

      static std::unique_ptr<instr> JUN_uptr(unsigned int a0) {
        return std::unique_ptr<instr>(new instr(JUN{a0}));
      }

      static std::unique_ptr<instr> JMS_uptr(unsigned int a0) {
        return std::unique_ptr<instr>(new instr(JMS{a0}));
      }

      static std::unique_ptr<instr> JCN_uptr(unsigned int a0, unsigned int a1) {
        return std::unique_ptr<instr>(new instr(JCN{a0, a1}));
      }

      static std::unique_ptr<instr> FIM_uptr(unsigned int a0, unsigned int a1) {
        return std::unique_ptr<instr>(new instr(FIM{a0, a1}));
      }

      static std::unique_ptr<instr> SRC_uptr(unsigned int a0) {
        return std::unique_ptr<instr>(new instr(SRC{a0}));
      }

      static std::unique_ptr<instr> FIN_uptr(unsigned int a0) {
        return std::unique_ptr<instr>(new instr(FIN{a0}));
      }

      static std::unique_ptr<instr> JIN_uptr(unsigned int a0) {
        return std::unique_ptr<instr>(new instr(JIN{a0}));
      }

      static std::unique_ptr<instr> ISZ_uptr(unsigned int a0, unsigned int a1) {
        return std::unique_ptr<instr>(new instr(ISZ{a0, a1}));
      }

      static std::unique_ptr<instr> BBL_uptr(unsigned int a0) {
        return std::unique_ptr<instr>(new instr(BBL{a0}));
      }
    };

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <
      typename T1, MapsTo<T1, unsigned int> F1, MapsTo<T1, unsigned int> F2,
      MapsTo<T1, unsigned int> F3, MapsTo<T1, unsigned int> F4,
      MapsTo<T1, unsigned int> F5, MapsTo<T1, unsigned int> F6,
      MapsTo<T1, unsigned int> F20, MapsTo<T1, unsigned int> F21,
      MapsTo<T1, unsigned int, unsigned int> F22,
      MapsTo<T1, unsigned int, unsigned int> F23, MapsTo<T1, unsigned int> F24,
      MapsTo<T1, unsigned int> F25, MapsTo<T1, unsigned int> F26,
      MapsTo<T1, unsigned int, unsigned int> F27, MapsTo<T1, unsigned int> F28>
  static T1 instr_rect(const T1 f, F1 &&f0, F2 &&f1, F3 &&f2, F4 &&f3, F5 &&f4,
                       F6 &&f5, const T1 f6, const T1 f7, const T1 f8,
                       const T1 f9, const T1 f10, const T1 f11, const T1 f12,
                       const T1 f13, const T1 f14, const T1 f15, const T1 f16,
                       const T1 f17, const T1 f18, F20 &&f19, F21 &&f20,
                       F22 &&f21, F23 &&f22, F24 &&f23, F25 &&f24, F26 &&f25,
                       F27 &&f26, F28 &&f27, const std::shared_ptr<instr> &i) {
    return std::visit(
        Overloaded{[&](const typename instr::NOP _args) -> T1 { return f; },
                   [&](const typename instr::LDM _args) -> T1 {
                     unsigned int n = _args.d_a0;
                     return f0(std::move(n));
                   },
                   [&](const typename instr::LD _args) -> T1 {
                     unsigned int r = _args.d_a0;
                     return f1(std::move(r));
                   },
                   [&](const typename instr::XCH _args) -> T1 {
                     unsigned int r = _args.d_a0;
                     return f2(std::move(r));
                   },
                   [&](const typename instr::INC _args) -> T1 {
                     unsigned int r = _args.d_a0;
                     return f3(std::move(r));
                   },
                   [&](const typename instr::ADD _args) -> T1 {
                     unsigned int r = _args.d_a0;
                     return f4(std::move(r));
                   },
                   [&](const typename instr::SUB _args) -> T1 {
                     unsigned int r = _args.d_a0;
                     return f5(std::move(r));
                   },
                   [&](const typename instr::IAC _args) -> T1 { return f6; },
                   [&](const typename instr::DAC _args) -> T1 { return f7; },
                   [&](const typename instr::CLC _args) -> T1 { return f8; },
                   [&](const typename instr::STC _args) -> T1 { return f9; },
                   [&](const typename instr::CMC _args) -> T1 { return f10; },
                   [&](const typename instr::CMA _args) -> T1 { return f11; },
                   [&](const typename instr::CLB _args) -> T1 { return f12; },
                   [&](const typename instr::RAL _args) -> T1 { return f13; },
                   [&](const typename instr::RAR _args) -> T1 { return f14; },
                   [&](const typename instr::TCC _args) -> T1 { return f15; },
                   [&](const typename instr::TCS _args) -> T1 { return f16; },
                   [&](const typename instr::DAA _args) -> T1 { return f17; },
                   [&](const typename instr::KBP _args) -> T1 { return f18; },
                   [&](const typename instr::JUN _args) -> T1 {
                     unsigned int a = _args.d_a0;
                     return f19(std::move(a));
                   },
                   [&](const typename instr::JMS _args) -> T1 {
                     unsigned int a = _args.d_a0;
                     return f20(std::move(a));
                   },
                   [&](const typename instr::JCN _args) -> T1 {
                     unsigned int c = _args.d_a0;
                     unsigned int a = _args.d_a1;
                     return f21(std::move(c), std::move(a));
                   },
                   [&](const typename instr::FIM _args) -> T1 {
                     unsigned int r = _args.d_a0;
                     unsigned int d = _args.d_a1;
                     return f22(std::move(r), std::move(d));
                   },
                   [&](const typename instr::SRC _args) -> T1 {
                     unsigned int r = _args.d_a0;
                     return f23(std::move(r));
                   },
                   [&](const typename instr::FIN _args) -> T1 {
                     unsigned int r = _args.d_a0;
                     return f24(std::move(r));
                   },
                   [&](const typename instr::JIN _args) -> T1 {
                     unsigned int r = _args.d_a0;
                     return f25(std::move(r));
                   },
                   [&](const typename instr::ISZ _args) -> T1 {
                     unsigned int r = _args.d_a0;
                     unsigned int a = _args.d_a1;
                     return f26(std::move(r), std::move(a));
                   },
                   [&](const typename instr::BBL _args) -> T1 {
                     unsigned int d = _args.d_a0;
                     return f27(std::move(d));
                   }},
        i->v());
  }

  template <
      typename T1, MapsTo<T1, unsigned int> F1, MapsTo<T1, unsigned int> F2,
      MapsTo<T1, unsigned int> F3, MapsTo<T1, unsigned int> F4,
      MapsTo<T1, unsigned int> F5, MapsTo<T1, unsigned int> F6,
      MapsTo<T1, unsigned int> F20, MapsTo<T1, unsigned int> F21,
      MapsTo<T1, unsigned int, unsigned int> F22,
      MapsTo<T1, unsigned int, unsigned int> F23, MapsTo<T1, unsigned int> F24,
      MapsTo<T1, unsigned int> F25, MapsTo<T1, unsigned int> F26,
      MapsTo<T1, unsigned int, unsigned int> F27, MapsTo<T1, unsigned int> F28>
  static T1 instr_rec(const T1 f, F1 &&f0, F2 &&f1, F3 &&f2, F4 &&f3, F5 &&f4,
                      F6 &&f5, const T1 f6, const T1 f7, const T1 f8,
                      const T1 f9, const T1 f10, const T1 f11, const T1 f12,
                      const T1 f13, const T1 f14, const T1 f15, const T1 f16,
                      const T1 f17, const T1 f18, F20 &&f19, F21 &&f20,
                      F22 &&f21, F23 &&f22, F24 &&f23, F25 &&f24, F26 &&f25,
                      F27 &&f26, F28 &&f27, const std::shared_ptr<instr> &i) {
    return std::visit(
        Overloaded{[&](const typename instr::NOP _args) -> T1 { return f; },
                   [&](const typename instr::LDM _args) -> T1 {
                     unsigned int n = _args.d_a0;
                     return f0(std::move(n));
                   },
                   [&](const typename instr::LD _args) -> T1 {
                     unsigned int r = _args.d_a0;
                     return f1(std::move(r));
                   },
                   [&](const typename instr::XCH _args) -> T1 {
                     unsigned int r = _args.d_a0;
                     return f2(std::move(r));
                   },
                   [&](const typename instr::INC _args) -> T1 {
                     unsigned int r = _args.d_a0;
                     return f3(std::move(r));
                   },
                   [&](const typename instr::ADD _args) -> T1 {
                     unsigned int r = _args.d_a0;
                     return f4(std::move(r));
                   },
                   [&](const typename instr::SUB _args) -> T1 {
                     unsigned int r = _args.d_a0;
                     return f5(std::move(r));
                   },
                   [&](const typename instr::IAC _args) -> T1 { return f6; },
                   [&](const typename instr::DAC _args) -> T1 { return f7; },
                   [&](const typename instr::CLC _args) -> T1 { return f8; },
                   [&](const typename instr::STC _args) -> T1 { return f9; },
                   [&](const typename instr::CMC _args) -> T1 { return f10; },
                   [&](const typename instr::CMA _args) -> T1 { return f11; },
                   [&](const typename instr::CLB _args) -> T1 { return f12; },
                   [&](const typename instr::RAL _args) -> T1 { return f13; },
                   [&](const typename instr::RAR _args) -> T1 { return f14; },
                   [&](const typename instr::TCC _args) -> T1 { return f15; },
                   [&](const typename instr::TCS _args) -> T1 { return f16; },
                   [&](const typename instr::DAA _args) -> T1 { return f17; },
                   [&](const typename instr::KBP _args) -> T1 { return f18; },
                   [&](const typename instr::JUN _args) -> T1 {
                     unsigned int a = _args.d_a0;
                     return f19(std::move(a));
                   },
                   [&](const typename instr::JMS _args) -> T1 {
                     unsigned int a = _args.d_a0;
                     return f20(std::move(a));
                   },
                   [&](const typename instr::JCN _args) -> T1 {
                     unsigned int c = _args.d_a0;
                     unsigned int a = _args.d_a1;
                     return f21(std::move(c), std::move(a));
                   },
                   [&](const typename instr::FIM _args) -> T1 {
                     unsigned int r = _args.d_a0;
                     unsigned int d = _args.d_a1;
                     return f22(std::move(r), std::move(d));
                   },
                   [&](const typename instr::SRC _args) -> T1 {
                     unsigned int r = _args.d_a0;
                     return f23(std::move(r));
                   },
                   [&](const typename instr::FIN _args) -> T1 {
                     unsigned int r = _args.d_a0;
                     return f24(std::move(r));
                   },
                   [&](const typename instr::JIN _args) -> T1 {
                     unsigned int r = _args.d_a0;
                     return f25(std::move(r));
                   },
                   [&](const typename instr::ISZ _args) -> T1 {
                     unsigned int r = _args.d_a0;
                     unsigned int a = _args.d_a1;
                     return f26(std::move(r), std::move(a));
                   },
                   [&](const typename instr::BBL _args) -> T1 {
                     unsigned int d = _args.d_a0;
                     return f27(std::move(d));
                   }},
        i->v());
  }

  static std::shared_ptr<state> execute(std::shared_ptr<state> s,
                                        const std::shared_ptr<instr> &i);
  static inline const std::shared_ptr<state> sample =
      std::make_shared<state>(state{
          3u,
          List<unsigned int>::ctor::Cons_(
              1u,
              List<unsigned int>::ctor::Cons_(
                  2u,
                  List<unsigned int>::ctor::Cons_(
                      3u,
                      List<unsigned int>::ctor::Cons_(
                          4u,
                          List<unsigned int>::ctor::Cons_(
                              5u, List<unsigned int>::ctor::Cons_(
                                      6u,
                                      List<unsigned int>::ctor::Cons_(
                                          7u,
                                          List<unsigned int>::ctor::Cons_(
                                              8u,
                                              List<unsigned int>::ctor::Cons_(
                                                  9u,
                                                  List<unsigned int>::ctor::Cons_(
                                                      10u,
                                                      List<unsigned int>::ctor::Cons_(
                                                          11u,
                                                          List<unsigned int>::ctor::Cons_(
                                                              12u,
                                                              List<unsigned int>::ctor::Cons_(
                                                                  13u,
                                                                  List<unsigned int>::ctor::Cons_(
                                                                      14u,
                                                                      List<unsigned int>::ctor::Cons_(
                                                                          15u,
                                                                          List<unsigned int>::ctor::Cons_(
                                                                              0u,
                                                                              List<
                                                                                  unsigned int>::ctor::
                                                                                  Nil_())))))))))))))))),
          false, 10u,
          List<unsigned int>::ctor::Cons_(
              20u, List<unsigned int>::ctor::Cons_(
                       30u, List<unsigned int>::ctor::Nil_())),
          42u,
          List<unsigned int>::ctor::Cons_(
              1u,
              List<unsigned int>::ctor::Cons_(
                  2u, List<unsigned int>::ctor::Cons_(
                          3u, List<unsigned int>::ctor::Cons_(
                                  4u, List<unsigned int>::ctor::Nil_()))))});
};

#endif // INCLUDED_GET_PAIR_BOUND_PROP
