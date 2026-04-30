#ifndef INCLUDED_INSTRUCTION_CLASSIFIERS
#define INCLUDED_INSTRUCTION_CLASSIFIERS

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

template <typename t_A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    t_A d_a0;
    std::unique_ptr<List<t_A>> d_a1;
  };

  using variant_t = std::variant<Nil, Cons>;

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

  List<t_A> &operator=(const List<t_A> &_other) {
    d_v_ = std::move(_other.clone().d_v_);
    return *this;
  }

  List<t_A> &operator=(List<t_A> &&_other) {
    d_v_ = std::move(_other.d_v_);
    return *this;
  }

  // ACCESSORS
  List<t_A> clone() const {
    List<t_A> _out{};

    struct _CloneFrame {
      const List<t_A> *_src;
      List<t_A> *_dst;
    };

    std::vector<_CloneFrame> _stack{};
    _stack.push_back({this, &_out});
    while (!_stack.empty()) {
      auto _frame = _stack.back();
      _stack.pop_back();
      const List<t_A> *_src = _frame._src;
      List<t_A> *_dst = _frame._dst;
      if (std::holds_alternative<Nil>(_src->v())) {
        _dst->d_v_ = Nil{};
      } else {
        const auto &_alt = std::get<Cons>(_src->v());
        _dst->d_v_ = Cons{_alt.d_a0,
                          _alt.d_a1 ? std::make_unique<List<t_A>>() : nullptr};
        auto &_dst_alt = std::get<Cons>(_dst->d_v_);
        if (_alt.d_a1) {
          _stack.push_back({_alt.d_a1.get(), _dst_alt.d_a1.get()});
        }
      }
    }
    return _out;
  }

  // CREATORS
  template <typename _U> explicit List(const List<_U> &_other) {
    if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
      d_v_ = Nil{};
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<_U>::Cons>(_other.v());
      d_v_ =
          Cons{t_A(d_a0), d_a1 ? std::make_unique<List<t_A>>(*d_a1) : nullptr};
    }
  }

  static List<t_A> nil() { return List(Nil{}); }

  static List<t_A> cons(t_A a0, List<t_A> a1) {
    return List(
        Cons{std::move(a0), std::make_unique<List<t_A>>(std::move(a1))});
  }

  // MANIPULATORS
  ~List() {
    std::vector<std::unique_ptr<List<t_A>>> _stack{};
    auto _drain = [&](List<t_A> &_node) {
      if (std::holds_alternative<Cons>(_node.d_v_)) {
        auto &_alt = std::get<Cons>(_node.d_v_);
        if (_alt.d_a1) {
          _stack.push_back(std::move(_alt.d_a1));
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

  inline variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  const variant_t &v() const { return d_v_; }
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
    instr_acc() {}

    explicit instr_acc(LDM _v) : d_v_(std::move(_v)) {}

    explicit instr_acc(LD _v) : d_v_(std::move(_v)) {}

    explicit instr_acc(ADD _v) : d_v_(std::move(_v)) {}

    explicit instr_acc(SUB _v) : d_v_(std::move(_v)) {}

    explicit instr_acc(INC _v) : d_v_(std::move(_v)) {}

    explicit instr_acc(XCH _v) : d_v_(std::move(_v)) {}

    explicit instr_acc(BBL _v) : d_v_(std::move(_v)) {}

    explicit instr_acc(SBM _v) : d_v_(_v) {}

    explicit instr_acc(RDM _v) : d_v_(_v) {}

    explicit instr_acc(RDR _v) : d_v_(_v) {}

    explicit instr_acc(ADM _v) : d_v_(_v) {}

    explicit instr_acc(RD0 _v) : d_v_(_v) {}

    explicit instr_acc(RD1 _v) : d_v_(_v) {}

    explicit instr_acc(RD2 _v) : d_v_(_v) {}

    explicit instr_acc(RD3 _v) : d_v_(_v) {}

    explicit instr_acc(CLB _v) : d_v_(_v) {}

    explicit instr_acc(CMA _v) : d_v_(_v) {}

    explicit instr_acc(IAC _v) : d_v_(_v) {}

    explicit instr_acc(DAC _v) : d_v_(_v) {}

    explicit instr_acc(RAL _v) : d_v_(_v) {}

    explicit instr_acc(RAR _v) : d_v_(_v) {}

    explicit instr_acc(TCC _v) : d_v_(_v) {}

    explicit instr_acc(TCS _v) : d_v_(_v) {}

    explicit instr_acc(DAA _v) : d_v_(_v) {}

    explicit instr_acc(KBP _v) : d_v_(_v) {}

    explicit instr_acc(NOP_acc _v) : d_v_(_v) {}

    instr_acc(const instr_acc &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    instr_acc(instr_acc &&_other) : d_v_(std::move(_other.d_v_)) {}

    instr_acc &operator=(const instr_acc &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    instr_acc &operator=(instr_acc &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    instr_acc clone() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<LDM>(_sv.v())) {
        const auto &[d_a0] = std::get<LDM>(_sv.v());
        return instr_acc(LDM{d_a0});
      } else if (std::holds_alternative<LD>(_sv.v())) {
        const auto &[d_a0] = std::get<LD>(_sv.v());
        return instr_acc(LD{d_a0});
      } else if (std::holds_alternative<ADD>(_sv.v())) {
        const auto &[d_a0] = std::get<ADD>(_sv.v());
        return instr_acc(ADD{d_a0});
      } else if (std::holds_alternative<SUB>(_sv.v())) {
        const auto &[d_a0] = std::get<SUB>(_sv.v());
        return instr_acc(SUB{d_a0});
      } else if (std::holds_alternative<INC>(_sv.v())) {
        const auto &[d_a0] = std::get<INC>(_sv.v());
        return instr_acc(INC{d_a0});
      } else if (std::holds_alternative<XCH>(_sv.v())) {
        const auto &[d_a0] = std::get<XCH>(_sv.v());
        return instr_acc(XCH{d_a0});
      } else if (std::holds_alternative<BBL>(_sv.v())) {
        const auto &[d_a0] = std::get<BBL>(_sv.v());
        return instr_acc(BBL{d_a0});
      } else if (std::holds_alternative<SBM>(_sv.v())) {
        return instr_acc(SBM{});
      } else if (std::holds_alternative<RDM>(_sv.v())) {
        return instr_acc(RDM{});
      } else if (std::holds_alternative<RDR>(_sv.v())) {
        return instr_acc(RDR{});
      } else if (std::holds_alternative<ADM>(_sv.v())) {
        return instr_acc(ADM{});
      } else if (std::holds_alternative<RD0>(_sv.v())) {
        return instr_acc(RD0{});
      } else if (std::holds_alternative<RD1>(_sv.v())) {
        return instr_acc(RD1{});
      } else if (std::holds_alternative<RD2>(_sv.v())) {
        return instr_acc(RD2{});
      } else if (std::holds_alternative<RD3>(_sv.v())) {
        return instr_acc(RD3{});
      } else if (std::holds_alternative<CLB>(_sv.v())) {
        return instr_acc(CLB{});
      } else if (std::holds_alternative<CMA>(_sv.v())) {
        return instr_acc(CMA{});
      } else if (std::holds_alternative<IAC>(_sv.v())) {
        return instr_acc(IAC{});
      } else if (std::holds_alternative<DAC>(_sv.v())) {
        return instr_acc(DAC{});
      } else if (std::holds_alternative<RAL>(_sv.v())) {
        return instr_acc(RAL{});
      } else if (std::holds_alternative<RAR>(_sv.v())) {
        return instr_acc(RAR{});
      } else if (std::holds_alternative<TCC>(_sv.v())) {
        return instr_acc(TCC{});
      } else if (std::holds_alternative<TCS>(_sv.v())) {
        return instr_acc(TCS{});
      } else if (std::holds_alternative<DAA>(_sv.v())) {
        return instr_acc(DAA{});
      } else if (std::holds_alternative<KBP>(_sv.v())) {
        return instr_acc(KBP{});
      } else {
        return instr_acc(NOP_acc{});
      }
    }

    // CREATORS
    static instr_acc ldm(unsigned int a0) {
      return instr_acc(LDM{std::move(a0)});
    }

    static instr_acc ld(unsigned int a0) {
      return instr_acc(LD{std::move(a0)});
    }

    static instr_acc add(unsigned int a0) {
      return instr_acc(ADD{std::move(a0)});
    }

    static instr_acc sub(unsigned int a0) {
      return instr_acc(SUB{std::move(a0)});
    }

    static instr_acc inc(unsigned int a0) {
      return instr_acc(INC{std::move(a0)});
    }

    static instr_acc xch(unsigned int a0) {
      return instr_acc(XCH{std::move(a0)});
    }

    static instr_acc bbl(unsigned int a0) {
      return instr_acc(BBL{std::move(a0)});
    }

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
    inline variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    const variant_t &v() const { return d_v_; }

    bool writes_acc() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename instr_acc::NOP_acc>(_sv.v())) {
        return false;
      } else {
        return true;
      }
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
      auto &&_sv = *(this);
      if (std::holds_alternative<typename instr_acc::LDM>(_sv.v())) {
        const auto &[d_a0] = std::get<typename instr_acc::LDM>(_sv.v());
        return f(d_a0);
      } else if (std::holds_alternative<typename instr_acc::LD>(_sv.v())) {
        const auto &[d_a0] = std::get<typename instr_acc::LD>(_sv.v());
        return f0(d_a0);
      } else if (std::holds_alternative<typename instr_acc::ADD>(_sv.v())) {
        const auto &[d_a0] = std::get<typename instr_acc::ADD>(_sv.v());
        return f1(d_a0);
      } else if (std::holds_alternative<typename instr_acc::SUB>(_sv.v())) {
        const auto &[d_a0] = std::get<typename instr_acc::SUB>(_sv.v());
        return f2(d_a0);
      } else if (std::holds_alternative<typename instr_acc::INC>(_sv.v())) {
        const auto &[d_a0] = std::get<typename instr_acc::INC>(_sv.v());
        return f3(d_a0);
      } else if (std::holds_alternative<typename instr_acc::XCH>(_sv.v())) {
        const auto &[d_a0] = std::get<typename instr_acc::XCH>(_sv.v());
        return f4(d_a0);
      } else if (std::holds_alternative<typename instr_acc::BBL>(_sv.v())) {
        const auto &[d_a0] = std::get<typename instr_acc::BBL>(_sv.v());
        return f5(d_a0);
      } else if (std::holds_alternative<typename instr_acc::SBM>(_sv.v())) {
        return f6;
      } else if (std::holds_alternative<typename instr_acc::RDM>(_sv.v())) {
        return f7;
      } else if (std::holds_alternative<typename instr_acc::RDR>(_sv.v())) {
        return f8;
      } else if (std::holds_alternative<typename instr_acc::ADM>(_sv.v())) {
        return f9;
      } else if (std::holds_alternative<typename instr_acc::RD0>(_sv.v())) {
        return f10;
      } else if (std::holds_alternative<typename instr_acc::RD1>(_sv.v())) {
        return f11;
      } else if (std::holds_alternative<typename instr_acc::RD2>(_sv.v())) {
        return f12;
      } else if (std::holds_alternative<typename instr_acc::RD3>(_sv.v())) {
        return f13;
      } else if (std::holds_alternative<typename instr_acc::CLB>(_sv.v())) {
        return f14;
      } else if (std::holds_alternative<typename instr_acc::CMA>(_sv.v())) {
        return f15;
      } else if (std::holds_alternative<typename instr_acc::IAC>(_sv.v())) {
        return f16;
      } else if (std::holds_alternative<typename instr_acc::DAC>(_sv.v())) {
        return f17;
      } else if (std::holds_alternative<typename instr_acc::RAL>(_sv.v())) {
        return f18;
      } else if (std::holds_alternative<typename instr_acc::RAR>(_sv.v())) {
        return f19;
      } else if (std::holds_alternative<typename instr_acc::TCC>(_sv.v())) {
        return f20;
      } else if (std::holds_alternative<typename instr_acc::TCS>(_sv.v())) {
        return f21;
      } else if (std::holds_alternative<typename instr_acc::DAA>(_sv.v())) {
        return f22;
      } else if (std::holds_alternative<typename instr_acc::KBP>(_sv.v())) {
        return f23;
      } else {
        return f24;
      }
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
      auto &&_sv = *(this);
      if (std::holds_alternative<typename instr_acc::LDM>(_sv.v())) {
        const auto &[d_a0] = std::get<typename instr_acc::LDM>(_sv.v());
        return f(d_a0);
      } else if (std::holds_alternative<typename instr_acc::LD>(_sv.v())) {
        const auto &[d_a0] = std::get<typename instr_acc::LD>(_sv.v());
        return f0(d_a0);
      } else if (std::holds_alternative<typename instr_acc::ADD>(_sv.v())) {
        const auto &[d_a0] = std::get<typename instr_acc::ADD>(_sv.v());
        return f1(d_a0);
      } else if (std::holds_alternative<typename instr_acc::SUB>(_sv.v())) {
        const auto &[d_a0] = std::get<typename instr_acc::SUB>(_sv.v());
        return f2(d_a0);
      } else if (std::holds_alternative<typename instr_acc::INC>(_sv.v())) {
        const auto &[d_a0] = std::get<typename instr_acc::INC>(_sv.v());
        return f3(d_a0);
      } else if (std::holds_alternative<typename instr_acc::XCH>(_sv.v())) {
        const auto &[d_a0] = std::get<typename instr_acc::XCH>(_sv.v());
        return f4(d_a0);
      } else if (std::holds_alternative<typename instr_acc::BBL>(_sv.v())) {
        const auto &[d_a0] = std::get<typename instr_acc::BBL>(_sv.v());
        return f5(d_a0);
      } else if (std::holds_alternative<typename instr_acc::SBM>(_sv.v())) {
        return f6;
      } else if (std::holds_alternative<typename instr_acc::RDM>(_sv.v())) {
        return f7;
      } else if (std::holds_alternative<typename instr_acc::RDR>(_sv.v())) {
        return f8;
      } else if (std::holds_alternative<typename instr_acc::ADM>(_sv.v())) {
        return f9;
      } else if (std::holds_alternative<typename instr_acc::RD0>(_sv.v())) {
        return f10;
      } else if (std::holds_alternative<typename instr_acc::RD1>(_sv.v())) {
        return f11;
      } else if (std::holds_alternative<typename instr_acc::RD2>(_sv.v())) {
        return f12;
      } else if (std::holds_alternative<typename instr_acc::RD3>(_sv.v())) {
        return f13;
      } else if (std::holds_alternative<typename instr_acc::CLB>(_sv.v())) {
        return f14;
      } else if (std::holds_alternative<typename instr_acc::CMA>(_sv.v())) {
        return f15;
      } else if (std::holds_alternative<typename instr_acc::IAC>(_sv.v())) {
        return f16;
      } else if (std::holds_alternative<typename instr_acc::DAC>(_sv.v())) {
        return f17;
      } else if (std::holds_alternative<typename instr_acc::RAL>(_sv.v())) {
        return f18;
      } else if (std::holds_alternative<typename instr_acc::RAR>(_sv.v())) {
        return f19;
      } else if (std::holds_alternative<typename instr_acc::TCC>(_sv.v())) {
        return f20;
      } else if (std::holds_alternative<typename instr_acc::TCS>(_sv.v())) {
        return f21;
      } else if (std::holds_alternative<typename instr_acc::DAA>(_sv.v())) {
        return f22;
      } else if (std::holds_alternative<typename instr_acc::KBP>(_sv.v())) {
        return f23;
      } else {
        return f24;
      }
    }
  };

  static unsigned int count_writes_acc(const List<instr_acc> &prog);
  static inline const unsigned int test_writes_acc =
      count_writes_acc(List<instr_acc>::cons(
          instr_acc::nop_acc(),
          List<instr_acc>::cons(
              instr_acc::ldm(9u),
              List<instr_acc>::cons(
                  instr_acc::rar(),
                  List<instr_acc>::cons(
                      instr_acc::kbp(),
                      List<instr_acc>::cons(
                          instr_acc::nop_acc(),
                          List<instr_acc>::cons(instr_acc::add(1u),
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
      unsigned int d_a0;
    };

    using variant_t =
        std::variant<WRM, WMP, WR0, WR1, WR2, WR3, NOP_ram, ADD_ram>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    instr_ram() {}

    explicit instr_ram(WRM _v) : d_v_(_v) {}

    explicit instr_ram(WMP _v) : d_v_(_v) {}

    explicit instr_ram(WR0 _v) : d_v_(_v) {}

    explicit instr_ram(WR1 _v) : d_v_(_v) {}

    explicit instr_ram(WR2 _v) : d_v_(_v) {}

    explicit instr_ram(WR3 _v) : d_v_(_v) {}

    explicit instr_ram(NOP_ram _v) : d_v_(_v) {}

    explicit instr_ram(ADD_ram _v) : d_v_(std::move(_v)) {}

    instr_ram(const instr_ram &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    instr_ram(instr_ram &&_other) : d_v_(std::move(_other.d_v_)) {}

    instr_ram &operator=(const instr_ram &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    instr_ram &operator=(instr_ram &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    instr_ram clone() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<WRM>(_sv.v())) {
        return instr_ram(WRM{});
      } else if (std::holds_alternative<WMP>(_sv.v())) {
        return instr_ram(WMP{});
      } else if (std::holds_alternative<WR0>(_sv.v())) {
        return instr_ram(WR0{});
      } else if (std::holds_alternative<WR1>(_sv.v())) {
        return instr_ram(WR1{});
      } else if (std::holds_alternative<WR2>(_sv.v())) {
        return instr_ram(WR2{});
      } else if (std::holds_alternative<WR3>(_sv.v())) {
        return instr_ram(WR3{});
      } else if (std::holds_alternative<NOP_ram>(_sv.v())) {
        return instr_ram(NOP_ram{});
      } else {
        const auto &[d_a0] = std::get<ADD_ram>(_sv.v());
        return instr_ram(ADD_ram{d_a0});
      }
    }

    // CREATORS
    static instr_ram wrm() { return instr_ram(WRM{}); }

    static instr_ram wmp() { return instr_ram(WMP{}); }

    static instr_ram wr0() { return instr_ram(WR0{}); }

    static instr_ram wr1() { return instr_ram(WR1{}); }

    static instr_ram wr2() { return instr_ram(WR2{}); }

    static instr_ram wr3() { return instr_ram(WR3{}); }

    static instr_ram nop_ram() { return instr_ram(NOP_ram{}); }

    static instr_ram add_ram(unsigned int a0) {
      return instr_ram(ADD_ram{std::move(a0)});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    const variant_t &v() const { return d_v_; }

    bool writes_ram() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename instr_ram::NOP_ram>(_sv.v())) {
        return false;
      } else if (std::holds_alternative<typename instr_ram::ADD_ram>(_sv.v())) {
        return false;
      } else {
        return true;
      }
    }

    template <typename T1, MapsTo<T1, unsigned int> F7>
    T1 instr_ram_rec(const T1 f, const T1 f0, const T1 f1, const T1 f2,
                     const T1 f3, const T1 f4, const T1 f5, F7 &&f6) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename instr_ram::WRM>(_sv.v())) {
        return f;
      } else if (std::holds_alternative<typename instr_ram::WMP>(_sv.v())) {
        return f0;
      } else if (std::holds_alternative<typename instr_ram::WR0>(_sv.v())) {
        return f1;
      } else if (std::holds_alternative<typename instr_ram::WR1>(_sv.v())) {
        return f2;
      } else if (std::holds_alternative<typename instr_ram::WR2>(_sv.v())) {
        return f3;
      } else if (std::holds_alternative<typename instr_ram::WR3>(_sv.v())) {
        return f4;
      } else if (std::holds_alternative<typename instr_ram::NOP_ram>(_sv.v())) {
        return f5;
      } else {
        const auto &[d_a0] = std::get<typename instr_ram::ADD_ram>(_sv.v());
        return f6(d_a0);
      }
    }

    template <typename T1, MapsTo<T1, unsigned int> F7>
    T1 instr_ram_rect(const T1 f, const T1 f0, const T1 f1, const T1 f2,
                      const T1 f3, const T1 f4, const T1 f5, F7 &&f6) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename instr_ram::WRM>(_sv.v())) {
        return f;
      } else if (std::holds_alternative<typename instr_ram::WMP>(_sv.v())) {
        return f0;
      } else if (std::holds_alternative<typename instr_ram::WR0>(_sv.v())) {
        return f1;
      } else if (std::holds_alternative<typename instr_ram::WR1>(_sv.v())) {
        return f2;
      } else if (std::holds_alternative<typename instr_ram::WR2>(_sv.v())) {
        return f3;
      } else if (std::holds_alternative<typename instr_ram::WR3>(_sv.v())) {
        return f4;
      } else if (std::holds_alternative<typename instr_ram::NOP_ram>(_sv.v())) {
        return f5;
      } else {
        const auto &[d_a0] = std::get<typename instr_ram::ADD_ram>(_sv.v());
        return f6(d_a0);
      }
    }
  };

  static unsigned int count_writes_ram(const List<instr_ram> &prog);
  static inline const unsigned int test_writes_ram =
      count_writes_ram(List<instr_ram>::cons(
          instr_ram::nop_ram(),
          List<instr_ram>::cons(
              instr_ram::wrm(),
              List<instr_ram>::cons(
                  instr_ram::add_ram(3u),
                  List<instr_ram>::cons(
                      instr_ram::wr3(),
                      List<instr_ram>::cons(
                          instr_ram::wmp(),
                          List<instr_ram>::cons(instr_ram::nop_ram(),
                                                List<instr_ram>::nil())))))));

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
    instr_regs() {}

    explicit instr_regs(XCH_regs _v) : d_v_(std::move(_v)) {}

    explicit instr_regs(INC_regs _v) : d_v_(std::move(_v)) {}

    explicit instr_regs(FIM _v) : d_v_(std::move(_v)) {}

    explicit instr_regs(FIN _v) : d_v_(std::move(_v)) {}

    explicit instr_regs(ISZ _v) : d_v_(std::move(_v)) {}

    explicit instr_regs(NOP_regs _v) : d_v_(_v) {}

    explicit instr_regs(ADD_regs _v) : d_v_(std::move(_v)) {}

    instr_regs(const instr_regs &_other)
        : d_v_(std::move(_other.clone().d_v_)) {}

    instr_regs(instr_regs &&_other) : d_v_(std::move(_other.d_v_)) {}

    instr_regs &operator=(const instr_regs &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    instr_regs &operator=(instr_regs &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    instr_regs clone() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<XCH_regs>(_sv.v())) {
        const auto &[d_a0] = std::get<XCH_regs>(_sv.v());
        return instr_regs(XCH_regs{d_a0});
      } else if (std::holds_alternative<INC_regs>(_sv.v())) {
        const auto &[d_a0] = std::get<INC_regs>(_sv.v());
        return instr_regs(INC_regs{d_a0});
      } else if (std::holds_alternative<FIM>(_sv.v())) {
        const auto &[d_a0, d_a1] = std::get<FIM>(_sv.v());
        return instr_regs(FIM{d_a0, d_a1});
      } else if (std::holds_alternative<FIN>(_sv.v())) {
        const auto &[d_a0] = std::get<FIN>(_sv.v());
        return instr_regs(FIN{d_a0});
      } else if (std::holds_alternative<ISZ>(_sv.v())) {
        const auto &[d_a0, d_a1] = std::get<ISZ>(_sv.v());
        return instr_regs(ISZ{d_a0, d_a1});
      } else if (std::holds_alternative<NOP_regs>(_sv.v())) {
        return instr_regs(NOP_regs{});
      } else {
        const auto &[d_a0] = std::get<ADD_regs>(_sv.v());
        return instr_regs(ADD_regs{d_a0});
      }
    }

    // CREATORS
    static instr_regs xch_regs(unsigned int a0) {
      return instr_regs(XCH_regs{std::move(a0)});
    }

    static instr_regs inc_regs(unsigned int a0) {
      return instr_regs(INC_regs{std::move(a0)});
    }

    static instr_regs fim(unsigned int a0, unsigned int a1) {
      return instr_regs(FIM{std::move(a0), std::move(a1)});
    }

    static instr_regs fin(unsigned int a0) {
      return instr_regs(FIN{std::move(a0)});
    }

    static instr_regs isz(unsigned int a0, unsigned int a1) {
      return instr_regs(ISZ{std::move(a0), std::move(a1)});
    }

    static instr_regs nop_regs() { return instr_regs(NOP_regs{}); }

    static instr_regs add_regs(unsigned int a0) {
      return instr_regs(ADD_regs{std::move(a0)});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    const variant_t &v() const { return d_v_; }

    bool writes_regs() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename instr_regs::NOP_regs>(_sv.v())) {
        return false;
      } else if (std::holds_alternative<typename instr_regs::ADD_regs>(
                     _sv.v())) {
        return false;
      } else {
        return true;
      }
    }

    template <
        typename T1, MapsTo<T1, unsigned int> F0, MapsTo<T1, unsigned int> F1,
        MapsTo<T1, unsigned int, unsigned int> F2, MapsTo<T1, unsigned int> F3,
        MapsTo<T1, unsigned int, unsigned int> F4, MapsTo<T1, unsigned int> F6>
    T1 instr_regs_rec(F0 &&f, F1 &&f0, F2 &&f1, F3 &&f2, F4 &&f3, const T1 f4,
                      F6 &&f5) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename instr_regs::XCH_regs>(_sv.v())) {
        const auto &[d_a0] = std::get<typename instr_regs::XCH_regs>(_sv.v());
        return f(d_a0);
      } else if (std::holds_alternative<typename instr_regs::INC_regs>(
                     _sv.v())) {
        const auto &[d_a0] = std::get<typename instr_regs::INC_regs>(_sv.v());
        return f0(d_a0);
      } else if (std::holds_alternative<typename instr_regs::FIM>(_sv.v())) {
        const auto &[d_a0, d_a1] = std::get<typename instr_regs::FIM>(_sv.v());
        return f1(d_a0, d_a1);
      } else if (std::holds_alternative<typename instr_regs::FIN>(_sv.v())) {
        const auto &[d_a0] = std::get<typename instr_regs::FIN>(_sv.v());
        return f2(d_a0);
      } else if (std::holds_alternative<typename instr_regs::ISZ>(_sv.v())) {
        const auto &[d_a0, d_a1] = std::get<typename instr_regs::ISZ>(_sv.v());
        return f3(d_a0, d_a1);
      } else if (std::holds_alternative<typename instr_regs::NOP_regs>(
                     _sv.v())) {
        return f4;
      } else {
        const auto &[d_a0] = std::get<typename instr_regs::ADD_regs>(_sv.v());
        return f5(d_a0);
      }
    }

    template <
        typename T1, MapsTo<T1, unsigned int> F0, MapsTo<T1, unsigned int> F1,
        MapsTo<T1, unsigned int, unsigned int> F2, MapsTo<T1, unsigned int> F3,
        MapsTo<T1, unsigned int, unsigned int> F4, MapsTo<T1, unsigned int> F6>
    T1 instr_regs_rect(F0 &&f, F1 &&f0, F2 &&f1, F3 &&f2, F4 &&f3, const T1 f4,
                       F6 &&f5) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename instr_regs::XCH_regs>(_sv.v())) {
        const auto &[d_a0] = std::get<typename instr_regs::XCH_regs>(_sv.v());
        return f(d_a0);
      } else if (std::holds_alternative<typename instr_regs::INC_regs>(
                     _sv.v())) {
        const auto &[d_a0] = std::get<typename instr_regs::INC_regs>(_sv.v());
        return f0(d_a0);
      } else if (std::holds_alternative<typename instr_regs::FIM>(_sv.v())) {
        const auto &[d_a0, d_a1] = std::get<typename instr_regs::FIM>(_sv.v());
        return f1(d_a0, d_a1);
      } else if (std::holds_alternative<typename instr_regs::FIN>(_sv.v())) {
        const auto &[d_a0] = std::get<typename instr_regs::FIN>(_sv.v());
        return f2(d_a0);
      } else if (std::holds_alternative<typename instr_regs::ISZ>(_sv.v())) {
        const auto &[d_a0, d_a1] = std::get<typename instr_regs::ISZ>(_sv.v());
        return f3(d_a0, d_a1);
      } else if (std::holds_alternative<typename instr_regs::NOP_regs>(
                     _sv.v())) {
        return f4;
      } else {
        const auto &[d_a0] = std::get<typename instr_regs::ADD_regs>(_sv.v());
        return f5(d_a0);
      }
    }
  };

  static unsigned int count_writes_regs(const List<instr_regs> &prog);
  static inline const unsigned int test_writes_regs =
      count_writes_regs(List<instr_regs>::cons(
          instr_regs::nop_regs(),
          List<instr_regs>::cons(
              instr_regs::fim(0u, 12u),
              List<instr_regs>::cons(
                  instr_regs::add_regs(1u),
                  List<instr_regs>::cons(
                      instr_regs::inc_regs(7u),
                      List<instr_regs>::cons(instr_regs::isz(1u, 2u),
                                             List<instr_regs>::nil()))))));

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
    instr_jump() {}

    explicit instr_jump(JCN _v) : d_v_(std::move(_v)) {}

    explicit instr_jump(JUN _v) : d_v_(std::move(_v)) {}

    explicit instr_jump(JMS _v) : d_v_(std::move(_v)) {}

    explicit instr_jump(JIN _v) : d_v_(std::move(_v)) {}

    explicit instr_jump(BBL_jump _v) : d_v_(std::move(_v)) {}

    explicit instr_jump(ISZ_jump _v) : d_v_(std::move(_v)) {}

    explicit instr_jump(ADD_jump _v) : d_v_(std::move(_v)) {}

    explicit instr_jump(NOP_jump _v) : d_v_(_v) {}

    instr_jump(const instr_jump &_other)
        : d_v_(std::move(_other.clone().d_v_)) {}

    instr_jump(instr_jump &&_other) : d_v_(std::move(_other.d_v_)) {}

    instr_jump &operator=(const instr_jump &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    instr_jump &operator=(instr_jump &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    instr_jump clone() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<JCN>(_sv.v())) {
        const auto &[d_a0, d_a1] = std::get<JCN>(_sv.v());
        return instr_jump(JCN{d_a0, d_a1});
      } else if (std::holds_alternative<JUN>(_sv.v())) {
        const auto &[d_a0] = std::get<JUN>(_sv.v());
        return instr_jump(JUN{d_a0});
      } else if (std::holds_alternative<JMS>(_sv.v())) {
        const auto &[d_a0] = std::get<JMS>(_sv.v());
        return instr_jump(JMS{d_a0});
      } else if (std::holds_alternative<JIN>(_sv.v())) {
        const auto &[d_a0] = std::get<JIN>(_sv.v());
        return instr_jump(JIN{d_a0});
      } else if (std::holds_alternative<BBL_jump>(_sv.v())) {
        const auto &[d_a0] = std::get<BBL_jump>(_sv.v());
        return instr_jump(BBL_jump{d_a0});
      } else if (std::holds_alternative<ISZ_jump>(_sv.v())) {
        const auto &[d_a0, d_a1] = std::get<ISZ_jump>(_sv.v());
        return instr_jump(ISZ_jump{d_a0, d_a1});
      } else if (std::holds_alternative<ADD_jump>(_sv.v())) {
        const auto &[d_a0] = std::get<ADD_jump>(_sv.v());
        return instr_jump(ADD_jump{d_a0});
      } else {
        return instr_jump(NOP_jump{});
      }
    }

    // CREATORS
    static instr_jump jcn(unsigned int a0, unsigned int a1) {
      return instr_jump(JCN{std::move(a0), std::move(a1)});
    }

    static instr_jump jun(unsigned int a0) {
      return instr_jump(JUN{std::move(a0)});
    }

    static instr_jump jms(unsigned int a0) {
      return instr_jump(JMS{std::move(a0)});
    }

    static instr_jump jin(unsigned int a0) {
      return instr_jump(JIN{std::move(a0)});
    }

    static instr_jump bbl_jump(unsigned int a0) {
      return instr_jump(BBL_jump{std::move(a0)});
    }

    static instr_jump isz_jump(unsigned int a0, unsigned int a1) {
      return instr_jump(ISZ_jump{std::move(a0), std::move(a1)});
    }

    static instr_jump add_jump(unsigned int a0) {
      return instr_jump(ADD_jump{std::move(a0)});
    }

    static instr_jump nop_jump() { return instr_jump(NOP_jump{}); }

    // MANIPULATORS
    inline variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    const variant_t &v() const { return d_v_; }

    bool is_jump() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename instr_jump::ADD_jump>(_sv.v())) {
        return false;
      } else if (std::holds_alternative<typename instr_jump::NOP_jump>(
                     _sv.v())) {
        return false;
      } else {
        return true;
      }
    }

    template <typename T1, MapsTo<T1, unsigned int, unsigned int> F0,
              MapsTo<T1, unsigned int> F1, MapsTo<T1, unsigned int> F2,
              MapsTo<T1, unsigned int> F3, MapsTo<T1, unsigned int> F4,
              MapsTo<T1, unsigned int, unsigned int> F5,
              MapsTo<T1, unsigned int> F6>
    T1 instr_jump_rec(F0 &&f, F1 &&f0, F2 &&f1, F3 &&f2, F4 &&f3, F5 &&f4,
                      F6 &&f5, const T1 f6) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename instr_jump::JCN>(_sv.v())) {
        const auto &[d_a0, d_a1] = std::get<typename instr_jump::JCN>(_sv.v());
        return f(d_a0, d_a1);
      } else if (std::holds_alternative<typename instr_jump::JUN>(_sv.v())) {
        const auto &[d_a0] = std::get<typename instr_jump::JUN>(_sv.v());
        return f0(d_a0);
      } else if (std::holds_alternative<typename instr_jump::JMS>(_sv.v())) {
        const auto &[d_a0] = std::get<typename instr_jump::JMS>(_sv.v());
        return f1(d_a0);
      } else if (std::holds_alternative<typename instr_jump::JIN>(_sv.v())) {
        const auto &[d_a0] = std::get<typename instr_jump::JIN>(_sv.v());
        return f2(d_a0);
      } else if (std::holds_alternative<typename instr_jump::BBL_jump>(
                     _sv.v())) {
        const auto &[d_a0] = std::get<typename instr_jump::BBL_jump>(_sv.v());
        return f3(d_a0);
      } else if (std::holds_alternative<typename instr_jump::ISZ_jump>(
                     _sv.v())) {
        const auto &[d_a0, d_a1] =
            std::get<typename instr_jump::ISZ_jump>(_sv.v());
        return f4(d_a0, d_a1);
      } else if (std::holds_alternative<typename instr_jump::ADD_jump>(
                     _sv.v())) {
        const auto &[d_a0] = std::get<typename instr_jump::ADD_jump>(_sv.v());
        return f5(d_a0);
      } else {
        return f6;
      }
    }

    template <typename T1, MapsTo<T1, unsigned int, unsigned int> F0,
              MapsTo<T1, unsigned int> F1, MapsTo<T1, unsigned int> F2,
              MapsTo<T1, unsigned int> F3, MapsTo<T1, unsigned int> F4,
              MapsTo<T1, unsigned int, unsigned int> F5,
              MapsTo<T1, unsigned int> F6>
    T1 instr_jump_rect(F0 &&f, F1 &&f0, F2 &&f1, F3 &&f2, F4 &&f3, F5 &&f4,
                       F6 &&f5, const T1 f6) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename instr_jump::JCN>(_sv.v())) {
        const auto &[d_a0, d_a1] = std::get<typename instr_jump::JCN>(_sv.v());
        return f(d_a0, d_a1);
      } else if (std::holds_alternative<typename instr_jump::JUN>(_sv.v())) {
        const auto &[d_a0] = std::get<typename instr_jump::JUN>(_sv.v());
        return f0(d_a0);
      } else if (std::holds_alternative<typename instr_jump::JMS>(_sv.v())) {
        const auto &[d_a0] = std::get<typename instr_jump::JMS>(_sv.v());
        return f1(d_a0);
      } else if (std::holds_alternative<typename instr_jump::JIN>(_sv.v())) {
        const auto &[d_a0] = std::get<typename instr_jump::JIN>(_sv.v());
        return f2(d_a0);
      } else if (std::holds_alternative<typename instr_jump::BBL_jump>(
                     _sv.v())) {
        const auto &[d_a0] = std::get<typename instr_jump::BBL_jump>(_sv.v());
        return f3(d_a0);
      } else if (std::holds_alternative<typename instr_jump::ISZ_jump>(
                     _sv.v())) {
        const auto &[d_a0, d_a1] =
            std::get<typename instr_jump::ISZ_jump>(_sv.v());
        return f4(d_a0, d_a1);
      } else if (std::holds_alternative<typename instr_jump::ADD_jump>(
                     _sv.v())) {
        const auto &[d_a0] = std::get<typename instr_jump::ADD_jump>(_sv.v());
        return f5(d_a0);
      } else {
        return f6;
      }
    }
  };

  static unsigned int count_jumps(const List<instr_jump> &prog);
  static inline const unsigned int test_jump_classifier =
      count_jumps(List<instr_jump>::cons(
          instr_jump::add_jump(0u),
          List<instr_jump>::cons(
              instr_jump::jcn(4u, 8u),
              List<instr_jump>::cons(
                  instr_jump::nop_jump(),
                  List<instr_jump>::cons(
                      instr_jump::jms(33u),
                      List<instr_jump>::cons(instr_jump::isz_jump(1u, 2u),
                                             List<instr_jump>::nil()))))));
  static inline const std::pair<
      std::pair<std::pair<unsigned int, unsigned int>, unsigned int>,
      unsigned int>
      t = std::make_pair(
          std::make_pair(std::make_pair(test_writes_acc, test_writes_ram),
                         test_writes_regs),
          test_jump_classifier);
};

#endif // INCLUDED_INSTRUCTION_CLASSIFIERS
