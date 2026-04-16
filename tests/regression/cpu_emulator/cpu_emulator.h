#ifndef INCLUDED_CPU_EMULATOR
#define INCLUDED_CPU_EMULATOR

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

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

public:
  // CREATORS
  explicit List(Nil _v) : d_v_(_v) {}

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

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }

  std::shared_ptr<List<t_A>> skipn(const unsigned int n) const {
    if (n <= 0) {
      return std::const_pointer_cast<List<t_A>>(this->shared_from_this());
    } else {
      unsigned int n0 = n - 1;
      if (std::holds_alternative<typename List<t_A>::Nil>(this->v())) {
        return List<t_A>::nil();
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<t_A>::Cons>(this->v());
        return d_a1->skipn(n0);
      }
    }
  }

  std::shared_ptr<List<t_A>> firstn(const unsigned int n) const {
    if (n <= 0) {
      return List<t_A>::nil();
    } else {
      unsigned int n0 = n - 1;
      if (std::holds_alternative<typename List<t_A>::Nil>(this->v())) {
        return List<t_A>::nil();
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<t_A>::Cons>(this->v());
        return List<t_A>::cons(d_a0, d_a1->firstn(n0));
      }
    }
  }
};

struct ListDef {
  template <typename T1>
  static T1 nth(const unsigned int n, const std::shared_ptr<List<T1>> &l,
                const T1 default0);
};

struct CpuEmulator {
  template <typename T1>
  static std::shared_ptr<List<T1>>
  update_nth(const unsigned int n, const T1 x,
             const std::shared_ptr<List<T1>> &l) {
    if (n <= 0) {
      if (std::holds_alternative<typename List<T1>::Nil>(l->v())) {
        return List<T1>::nil();
      } else {
        const auto &[d_a0, d_a1] = std::get<typename List<T1>::Cons>(l->v());
        return List<T1>::cons(x, d_a1);
      }
    } else {
      unsigned int n_ = n - 1;
      if (std::holds_alternative<typename List<T1>::Nil>(l->v())) {
        return List<T1>::nil();
      } else {
        const auto &[d_a00, d_a10] = std::get<typename List<T1>::Cons>(l->v());
        return List<T1>::cons(d_a00, update_nth<T1>(n_, x, d_a10));
      }
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
  push_return(const std::shared_ptr<state> &s, const unsigned int ret);

  struct instr {
    // TYPES
    struct NOP {};

    struct LDM {
      unsigned int d_n;
    };

    struct LD {
      unsigned int d_r;
    };

    struct XCH {
      unsigned int d_r;
    };

    struct INC {
      unsigned int d_r;
    };

    struct ADD {
      unsigned int d_r;
    };

    struct SUB {
      unsigned int d_r;
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
      unsigned int d_a;
    };

    struct JMS {
      unsigned int d_a;
    };

    struct JCN {
      unsigned int d_c;
      unsigned int d_a;
    };

    struct FIM {
      unsigned int d_r;
      unsigned int d_d;
    };

    struct SRC {
      unsigned int d_r;
    };

    struct FIN {
      unsigned int d_r;
    };

    struct JIN {
      unsigned int d_r;
    };

    struct ISZ {
      unsigned int d_r;
      unsigned int d_a;
    };

    struct BBL {
      unsigned int d_d;
    };

    using variant_t =
        std::variant<NOP, LDM, LD, XCH, INC, ADD, SUB, IAC, DAC, CLC, STC, CMC,
                     CMA, CLB, RAL, RAR, TCC, TCS, DAA, KBP, JUN, JMS, JCN, FIM,
                     SRC, FIN, JIN, ISZ, BBL>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    explicit instr(NOP _v) : d_v_(_v) {}

    explicit instr(LDM _v) : d_v_(std::move(_v)) {}

    explicit instr(LD _v) : d_v_(std::move(_v)) {}

    explicit instr(XCH _v) : d_v_(std::move(_v)) {}

    explicit instr(INC _v) : d_v_(std::move(_v)) {}

    explicit instr(ADD _v) : d_v_(std::move(_v)) {}

    explicit instr(SUB _v) : d_v_(std::move(_v)) {}

    explicit instr(IAC _v) : d_v_(_v) {}

    explicit instr(DAC _v) : d_v_(_v) {}

    explicit instr(CLC _v) : d_v_(_v) {}

    explicit instr(STC _v) : d_v_(_v) {}

    explicit instr(CMC _v) : d_v_(_v) {}

    explicit instr(CMA _v) : d_v_(_v) {}

    explicit instr(CLB _v) : d_v_(_v) {}

    explicit instr(RAL _v) : d_v_(_v) {}

    explicit instr(RAR _v) : d_v_(_v) {}

    explicit instr(TCC _v) : d_v_(_v) {}

    explicit instr(TCS _v) : d_v_(_v) {}

    explicit instr(DAA _v) : d_v_(_v) {}

    explicit instr(KBP _v) : d_v_(_v) {}

    explicit instr(JUN _v) : d_v_(std::move(_v)) {}

    explicit instr(JMS _v) : d_v_(std::move(_v)) {}

    explicit instr(JCN _v) : d_v_(std::move(_v)) {}

    explicit instr(FIM _v) : d_v_(std::move(_v)) {}

    explicit instr(SRC _v) : d_v_(std::move(_v)) {}

    explicit instr(FIN _v) : d_v_(std::move(_v)) {}

    explicit instr(JIN _v) : d_v_(std::move(_v)) {}

    explicit instr(ISZ _v) : d_v_(std::move(_v)) {}

    explicit instr(BBL _v) : d_v_(std::move(_v)) {}

    static std::shared_ptr<instr> nop() {
      return std::make_shared<instr>(NOP{});
    }

    static std::shared_ptr<instr> ldm(unsigned int n) {
      return std::make_shared<instr>(LDM{std::move(n)});
    }

    static std::shared_ptr<instr> ld(unsigned int r) {
      return std::make_shared<instr>(LD{std::move(r)});
    }

    static std::shared_ptr<instr> xch(unsigned int r) {
      return std::make_shared<instr>(XCH{std::move(r)});
    }

    static std::shared_ptr<instr> inc(unsigned int r) {
      return std::make_shared<instr>(INC{std::move(r)});
    }

    static std::shared_ptr<instr> add(unsigned int r) {
      return std::make_shared<instr>(ADD{std::move(r)});
    }

    static std::shared_ptr<instr> sub(unsigned int r) {
      return std::make_shared<instr>(SUB{std::move(r)});
    }

    static std::shared_ptr<instr> iac() {
      return std::make_shared<instr>(IAC{});
    }

    static std::shared_ptr<instr> dac() {
      return std::make_shared<instr>(DAC{});
    }

    static std::shared_ptr<instr> clc() {
      return std::make_shared<instr>(CLC{});
    }

    static std::shared_ptr<instr> stc() {
      return std::make_shared<instr>(STC{});
    }

    static std::shared_ptr<instr> cmc() {
      return std::make_shared<instr>(CMC{});
    }

    static std::shared_ptr<instr> cma() {
      return std::make_shared<instr>(CMA{});
    }

    static std::shared_ptr<instr> clb() {
      return std::make_shared<instr>(CLB{});
    }

    static std::shared_ptr<instr> ral() {
      return std::make_shared<instr>(RAL{});
    }

    static std::shared_ptr<instr> rar() {
      return std::make_shared<instr>(RAR{});
    }

    static std::shared_ptr<instr> tcc() {
      return std::make_shared<instr>(TCC{});
    }

    static std::shared_ptr<instr> tcs() {
      return std::make_shared<instr>(TCS{});
    }

    static std::shared_ptr<instr> daa() {
      return std::make_shared<instr>(DAA{});
    }

    static std::shared_ptr<instr> kbp() {
      return std::make_shared<instr>(KBP{});
    }

    static std::shared_ptr<instr> jun(unsigned int a) {
      return std::make_shared<instr>(JUN{std::move(a)});
    }

    static std::shared_ptr<instr> jms(unsigned int a) {
      return std::make_shared<instr>(JMS{std::move(a)});
    }

    static std::shared_ptr<instr> jcn(unsigned int c, unsigned int a) {
      return std::make_shared<instr>(JCN{std::move(c), std::move(a)});
    }

    static std::shared_ptr<instr> fim(unsigned int r, unsigned int d) {
      return std::make_shared<instr>(FIM{std::move(r), std::move(d)});
    }

    static std::shared_ptr<instr> src(unsigned int r) {
      return std::make_shared<instr>(SRC{std::move(r)});
    }

    static std::shared_ptr<instr> fin(unsigned int r) {
      return std::make_shared<instr>(FIN{std::move(r)});
    }

    static std::shared_ptr<instr> jin(unsigned int r) {
      return std::make_shared<instr>(JIN{std::move(r)});
    }

    static std::shared_ptr<instr> isz(unsigned int r, unsigned int a) {
      return std::make_shared<instr>(ISZ{std::move(r), std::move(a)});
    }

    static std::shared_ptr<instr> bbl(unsigned int d) {
      return std::make_shared<instr>(BBL{std::move(d)});
    }

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
    if (std::holds_alternative<typename instr::NOP>(i->v())) {
      return f;
    } else if (std::holds_alternative<typename instr::LDM>(i->v())) {
      const auto &[d_n] = std::get<typename instr::LDM>(i->v());
      return f0(d_n);
    } else if (std::holds_alternative<typename instr::LD>(i->v())) {
      const auto &[d_r] = std::get<typename instr::LD>(i->v());
      return f1(d_r);
    } else if (std::holds_alternative<typename instr::XCH>(i->v())) {
      const auto &[d_r] = std::get<typename instr::XCH>(i->v());
      return f2(d_r);
    } else if (std::holds_alternative<typename instr::INC>(i->v())) {
      const auto &[d_r] = std::get<typename instr::INC>(i->v());
      return f3(d_r);
    } else if (std::holds_alternative<typename instr::ADD>(i->v())) {
      const auto &[d_r] = std::get<typename instr::ADD>(i->v());
      return f4(d_r);
    } else if (std::holds_alternative<typename instr::SUB>(i->v())) {
      const auto &[d_r] = std::get<typename instr::SUB>(i->v());
      return f5(d_r);
    } else if (std::holds_alternative<typename instr::IAC>(i->v())) {
      return f6;
    } else if (std::holds_alternative<typename instr::DAC>(i->v())) {
      return f7;
    } else if (std::holds_alternative<typename instr::CLC>(i->v())) {
      return f8;
    } else if (std::holds_alternative<typename instr::STC>(i->v())) {
      return f9;
    } else if (std::holds_alternative<typename instr::CMC>(i->v())) {
      return f10;
    } else if (std::holds_alternative<typename instr::CMA>(i->v())) {
      return f11;
    } else if (std::holds_alternative<typename instr::CLB>(i->v())) {
      return f12;
    } else if (std::holds_alternative<typename instr::RAL>(i->v())) {
      return f13;
    } else if (std::holds_alternative<typename instr::RAR>(i->v())) {
      return f14;
    } else if (std::holds_alternative<typename instr::TCC>(i->v())) {
      return f15;
    } else if (std::holds_alternative<typename instr::TCS>(i->v())) {
      return f16;
    } else if (std::holds_alternative<typename instr::DAA>(i->v())) {
      return f17;
    } else if (std::holds_alternative<typename instr::KBP>(i->v())) {
      return f18;
    } else if (std::holds_alternative<typename instr::JUN>(i->v())) {
      const auto &[d_a] = std::get<typename instr::JUN>(i->v());
      return f19(d_a);
    } else if (std::holds_alternative<typename instr::JMS>(i->v())) {
      const auto &[d_a] = std::get<typename instr::JMS>(i->v());
      return f20(d_a);
    } else if (std::holds_alternative<typename instr::JCN>(i->v())) {
      const auto &[d_c, d_a] = std::get<typename instr::JCN>(i->v());
      return f21(d_c, d_a);
    } else if (std::holds_alternative<typename instr::FIM>(i->v())) {
      const auto &[d_r, d_d] = std::get<typename instr::FIM>(i->v());
      return f22(d_r, d_d);
    } else if (std::holds_alternative<typename instr::SRC>(i->v())) {
      const auto &[d_r] = std::get<typename instr::SRC>(i->v());
      return f23(d_r);
    } else if (std::holds_alternative<typename instr::FIN>(i->v())) {
      const auto &[d_r] = std::get<typename instr::FIN>(i->v());
      return f24(d_r);
    } else if (std::holds_alternative<typename instr::JIN>(i->v())) {
      const auto &[d_r] = std::get<typename instr::JIN>(i->v());
      return f25(d_r);
    } else if (std::holds_alternative<typename instr::ISZ>(i->v())) {
      const auto &[d_r, d_a] = std::get<typename instr::ISZ>(i->v());
      return f26(d_r, d_a);
    } else {
      const auto &[d_d] = std::get<typename instr::BBL>(i->v());
      return f27(d_d);
    }
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
    if (std::holds_alternative<typename instr::NOP>(i->v())) {
      return f;
    } else if (std::holds_alternative<typename instr::LDM>(i->v())) {
      const auto &[d_n] = std::get<typename instr::LDM>(i->v());
      return f0(d_n);
    } else if (std::holds_alternative<typename instr::LD>(i->v())) {
      const auto &[d_r] = std::get<typename instr::LD>(i->v());
      return f1(d_r);
    } else if (std::holds_alternative<typename instr::XCH>(i->v())) {
      const auto &[d_r] = std::get<typename instr::XCH>(i->v());
      return f2(d_r);
    } else if (std::holds_alternative<typename instr::INC>(i->v())) {
      const auto &[d_r] = std::get<typename instr::INC>(i->v());
      return f3(d_r);
    } else if (std::holds_alternative<typename instr::ADD>(i->v())) {
      const auto &[d_r] = std::get<typename instr::ADD>(i->v());
      return f4(d_r);
    } else if (std::holds_alternative<typename instr::SUB>(i->v())) {
      const auto &[d_r] = std::get<typename instr::SUB>(i->v());
      return f5(d_r);
    } else if (std::holds_alternative<typename instr::IAC>(i->v())) {
      return f6;
    } else if (std::holds_alternative<typename instr::DAC>(i->v())) {
      return f7;
    } else if (std::holds_alternative<typename instr::CLC>(i->v())) {
      return f8;
    } else if (std::holds_alternative<typename instr::STC>(i->v())) {
      return f9;
    } else if (std::holds_alternative<typename instr::CMC>(i->v())) {
      return f10;
    } else if (std::holds_alternative<typename instr::CMA>(i->v())) {
      return f11;
    } else if (std::holds_alternative<typename instr::CLB>(i->v())) {
      return f12;
    } else if (std::holds_alternative<typename instr::RAL>(i->v())) {
      return f13;
    } else if (std::holds_alternative<typename instr::RAR>(i->v())) {
      return f14;
    } else if (std::holds_alternative<typename instr::TCC>(i->v())) {
      return f15;
    } else if (std::holds_alternative<typename instr::TCS>(i->v())) {
      return f16;
    } else if (std::holds_alternative<typename instr::DAA>(i->v())) {
      return f17;
    } else if (std::holds_alternative<typename instr::KBP>(i->v())) {
      return f18;
    } else if (std::holds_alternative<typename instr::JUN>(i->v())) {
      const auto &[d_a] = std::get<typename instr::JUN>(i->v());
      return f19(d_a);
    } else if (std::holds_alternative<typename instr::JMS>(i->v())) {
      const auto &[d_a] = std::get<typename instr::JMS>(i->v());
      return f20(d_a);
    } else if (std::holds_alternative<typename instr::JCN>(i->v())) {
      const auto &[d_c, d_a] = std::get<typename instr::JCN>(i->v());
      return f21(d_c, d_a);
    } else if (std::holds_alternative<typename instr::FIM>(i->v())) {
      const auto &[d_r, d_d] = std::get<typename instr::FIM>(i->v());
      return f22(d_r, d_d);
    } else if (std::holds_alternative<typename instr::SRC>(i->v())) {
      const auto &[d_r] = std::get<typename instr::SRC>(i->v());
      return f23(d_r);
    } else if (std::holds_alternative<typename instr::FIN>(i->v())) {
      const auto &[d_r] = std::get<typename instr::FIN>(i->v());
      return f24(d_r);
    } else if (std::holds_alternative<typename instr::JIN>(i->v())) {
      const auto &[d_r] = std::get<typename instr::JIN>(i->v());
      return f25(d_r);
    } else if (std::holds_alternative<typename instr::ISZ>(i->v())) {
      const auto &[d_r, d_a] = std::get<typename instr::ISZ>(i->v());
      return f26(d_r, d_a);
    } else {
      const auto &[d_d] = std::get<typename instr::BBL>(i->v());
      return f27(d_d);
    }
  }

  static std::shared_ptr<state> execute(const std::shared_ptr<state> &s,
                                        const std::shared_ptr<instr> &i);
  static inline const std::shared_ptr<state> sample =
      std::make_shared<state>(state{
          3u,
          List<unsigned int>::cons(
              1u,
              List<unsigned int>::cons(
                  2u,
                  List<unsigned int>::cons(
                      3u,
                      List<unsigned int>::cons(
                          4u,
                          List<unsigned int>::cons(
                              5u,
                              List<unsigned int>::cons(
                                  6u,
                                  List<unsigned int>::cons(
                                      7u, List<unsigned int>::cons(
                                              8u,
                                              List<unsigned int>::cons(
                                                  9u,
                                                  List<unsigned int>::cons(
                                                      10u,
                                                      List<unsigned int>::cons(
                                                          11u,
                                                          List<unsigned int>::cons(
                                                              12u,
                                                              List<unsigned int>::cons(
                                                                  13u,
                                                                  List<unsigned int>::cons(
                                                                      14u,
                                                                      List<unsigned int>::cons(
                                                                          15u,
                                                                          List<unsigned int>::cons(
                                                                              0u,
                                                                              List<
                                                                                  unsigned int>::
                                                                                  nil())))))))))))))))),
          false, 10u,
          List<unsigned int>::cons(
              20u, List<unsigned int>::cons(30u, List<unsigned int>::nil())),
          42u,
          List<unsigned int>::cons(
              1u, List<unsigned int>::cons(
                      2u, List<unsigned int>::cons(
                              3u, List<unsigned int>::cons(
                                      4u, List<unsigned int>::nil()))))});
  static inline const unsigned int add_result =
      execute(sample, instr::add(4u))->ex_acc;
  static inline const unsigned int nop_acc =
      execute(sample, instr::nop())->ex_acc;
  static inline const unsigned int ldm_result =
      execute(sample, instr::ldm(5u))->ex_acc;
  static inline const unsigned int jun_pc =
      execute(sample, instr::jun(1024u))->ex_pc;
};

template <typename T1>
T1 ListDef::nth(const unsigned int n, const std::shared_ptr<List<T1>> &l,
                const T1 default0) {
  if (n <= 0) {
    if (std::holds_alternative<typename List<T1>::Nil>(l->v())) {
      return default0;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<T1>::Cons>(l->v());
      return d_a0;
    }
  } else {
    unsigned int m = n - 1;
    if (std::holds_alternative<typename List<T1>::Nil>(l->v())) {
      return default0;
    } else {
      const auto &[d_a00, d_a10] = std::get<typename List<T1>::Cons>(l->v());
      return ListDef::template nth<T1>(m, d_a10, default0);
    }
  }
}

#endif // INCLUDED_CPU_EMULATOR
