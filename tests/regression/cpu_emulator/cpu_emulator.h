#ifndef INCLUDED_CPU_EMULATOR
#define INCLUDED_CPU_EMULATOR

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

  List(List<A> &&_other) : v_(std::move(_other.v_)) {}

  List<A> &operator=(const List<A> &_other) {
    v_ = std::move(_other.clone().v_);
    return *this;
  }

  List<A> &operator=(List<A> &&_other) {
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

  List<A> skipn(unsigned int n) const {
    if (n <= 0) {
      return std::move(*this);
    } else {
      unsigned int n0 = n - 1;
      if (std::holds_alternative<typename List<A>::Nil>(this->v())) {
        return List<A>::nil();
      } else {
        auto &[a0, a1] = std::get<typename List<A>::Cons>(this->v());
        return (*a1).skipn(n0);
      }
    }
  }

  List<A> firstn(unsigned int n) const {
    if (n <= 0) {
      return List<A>::nil();
    } else {
      unsigned int n0 = n - 1;
      if (std::holds_alternative<typename List<A>::Nil>(this->v())) {
        return List<A>::nil();
      } else {
        const auto &[a0, a1] = std::get<typename List<A>::Cons>(this->v());
        return List<A>::cons(a0, (*a1).firstn(n0));
      }
    }
  }
};

struct ListDef {
  template <typename T1>
  static T1 nth(unsigned int n, const List<T1> &l, T1 default0);
};

struct CpuEmulator {
  template <typename T1>
  static List<T1> update_nth(unsigned int n, T1 x, const List<T1> &l) {
    if (n <= 0) {
      if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
        return List<T1>::nil();
      } else {
        const auto &[a0, a1] = std::get<typename List<T1>::Cons>(l.v());
        return List<T1>::cons(x, *a1);
      }
    } else {
      unsigned int n_ = n - 1;
      if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
        return List<T1>::nil();
      } else {
        const auto &[a00, a10] = std::get<typename List<T1>::Cons>(l.v());
        return List<T1>::cons(a00, update_nth<T1>(n_, x, *a10));
      }
    }
  }

  struct state {
    unsigned int ex_acc;
    List<unsigned int> ex_regs;
    bool ex_carry;
    unsigned int ex_pc;
    List<unsigned int> ex_stack;
    unsigned int ex_pair_bus;
    List<unsigned int> ex_ports;

    // ACCESSORS
    state clone() const {
      return state{(*this).ex_acc,           (*this).ex_regs.clone(),
                   (*this).ex_carry,         (*this).ex_pc,
                   (*this).ex_stack.clone(), (*this).ex_pair_bus,
                   (*this).ex_ports.clone()};
    }
  };

  static unsigned int get_reg(const state &s, unsigned int r);
  static List<unsigned int> set_reg(const state &s, unsigned int r,
                                    unsigned int v);
  static unsigned int pair_base(unsigned int r);
  static unsigned int get_pair(const state &s, unsigned int r);
  static List<unsigned int> set_pair(const state &s, unsigned int r,
                                     unsigned int v);
  static List<unsigned int> push_return(const state &s, unsigned int ret);

  struct instr {
    // TYPES
    struct NOP {};

    struct LDM {
      unsigned int n;
    };

    struct LD {
      unsigned int r;
    };

    struct XCH {
      unsigned int r;
    };

    struct INC {
      unsigned int r;
    };

    struct ADD {
      unsigned int r;
    };

    struct SUB {
      unsigned int r;
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
      unsigned int a;
    };

    struct JMS {
      unsigned int a;
    };

    struct JCN {
      unsigned int c;
      unsigned int a;
    };

    struct FIM {
      unsigned int r;
      unsigned int d;
    };

    struct SRC {
      unsigned int r;
    };

    struct FIN {
      unsigned int r;
    };

    struct JIN {
      unsigned int r;
    };

    struct ISZ {
      unsigned int r;
      unsigned int a;
    };

    struct BBL {
      unsigned int d;
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

    instr(const instr &_other) : v_(std::move(_other.clone().v_)) {}

    instr(instr &&_other) : v_(std::move(_other.v_)) {}

    instr &operator=(const instr &_other) {
      v_ = std::move(_other.clone().v_);
      return *this;
    }

    instr &operator=(instr &&_other) {
      v_ = std::move(_other.v_);
      return *this;
    }

    // ACCESSORS
    instr clone() const {
      if (std::holds_alternative<NOP>(this->v())) {
        return instr(NOP{});
      } else if (std::holds_alternative<LDM>(this->v())) {
        const auto &[n] = std::get<LDM>(this->v());
        return instr(LDM{n});
      } else if (std::holds_alternative<LD>(this->v())) {
        const auto &[r] = std::get<LD>(this->v());
        return instr(LD{r});
      } else if (std::holds_alternative<XCH>(this->v())) {
        const auto &[r] = std::get<XCH>(this->v());
        return instr(XCH{r});
      } else if (std::holds_alternative<INC>(this->v())) {
        const auto &[r] = std::get<INC>(this->v());
        return instr(INC{r});
      } else if (std::holds_alternative<ADD>(this->v())) {
        const auto &[r] = std::get<ADD>(this->v());
        return instr(ADD{r});
      } else if (std::holds_alternative<SUB>(this->v())) {
        const auto &[r] = std::get<SUB>(this->v());
        return instr(SUB{r});
      } else if (std::holds_alternative<IAC>(this->v())) {
        return instr(IAC{});
      } else if (std::holds_alternative<DAC>(this->v())) {
        return instr(DAC{});
      } else if (std::holds_alternative<CLC>(this->v())) {
        return instr(CLC{});
      } else if (std::holds_alternative<STC>(this->v())) {
        return instr(STC{});
      } else if (std::holds_alternative<CMC>(this->v())) {
        return instr(CMC{});
      } else if (std::holds_alternative<CMA>(this->v())) {
        return instr(CMA{});
      } else if (std::holds_alternative<CLB>(this->v())) {
        return instr(CLB{});
      } else if (std::holds_alternative<RAL>(this->v())) {
        return instr(RAL{});
      } else if (std::holds_alternative<RAR>(this->v())) {
        return instr(RAR{});
      } else if (std::holds_alternative<TCC>(this->v())) {
        return instr(TCC{});
      } else if (std::holds_alternative<TCS>(this->v())) {
        return instr(TCS{});
      } else if (std::holds_alternative<DAA>(this->v())) {
        return instr(DAA{});
      } else if (std::holds_alternative<KBP>(this->v())) {
        return instr(KBP{});
      } else if (std::holds_alternative<JUN>(this->v())) {
        const auto &[a] = std::get<JUN>(this->v());
        return instr(JUN{a});
      } else if (std::holds_alternative<JMS>(this->v())) {
        const auto &[a] = std::get<JMS>(this->v());
        return instr(JMS{a});
      } else if (std::holds_alternative<JCN>(this->v())) {
        const auto &[c, a] = std::get<JCN>(this->v());
        return instr(JCN{c, a});
      } else if (std::holds_alternative<FIM>(this->v())) {
        const auto &[r, d] = std::get<FIM>(this->v());
        return instr(FIM{r, d});
      } else if (std::holds_alternative<SRC>(this->v())) {
        const auto &[r] = std::get<SRC>(this->v());
        return instr(SRC{r});
      } else if (std::holds_alternative<FIN>(this->v())) {
        const auto &[r] = std::get<FIN>(this->v());
        return instr(FIN{r});
      } else if (std::holds_alternative<JIN>(this->v())) {
        const auto &[r] = std::get<JIN>(this->v());
        return instr(JIN{r});
      } else if (std::holds_alternative<ISZ>(this->v())) {
        const auto &[r, a] = std::get<ISZ>(this->v());
        return instr(ISZ{r, a});
      } else {
        const auto &[d] = std::get<BBL>(this->v());
        return instr(BBL{d});
      }
    }

    // CREATORS
    static instr nop() { return instr(NOP{}); }

    static instr ldm(unsigned int n) { return instr(LDM{n}); }

    static instr ld(unsigned int r) { return instr(LD{r}); }

    static instr xch(unsigned int r) { return instr(XCH{r}); }

    static instr inc(unsigned int r) { return instr(INC{r}); }

    static instr add(unsigned int r) { return instr(ADD{r}); }

    static instr sub(unsigned int r) { return instr(SUB{r}); }

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

    static instr jun(unsigned int a) { return instr(JUN{a}); }

    static instr jms(unsigned int a) { return instr(JMS{a}); }

    static instr jcn(unsigned int c, unsigned int a) {
      return instr(JCN{c, a});
    }

    static instr fim(unsigned int r, unsigned int d) {
      return instr(FIM{r, d});
    }

    static instr src(unsigned int r) { return instr(SRC{r}); }

    static instr fin(unsigned int r) { return instr(FIN{r}); }

    static instr jin(unsigned int r) { return instr(JIN{r}); }

    static instr isz(unsigned int r, unsigned int a) {
      return instr(ISZ{r, a});
    }

    static instr bbl(unsigned int d) { return instr(BBL{d}); }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename F1, typename F2, typename F3, typename F4,
            typename F5, typename F6, typename F20, typename F21, typename F22,
            typename F23, typename F24, typename F25, typename F26,
            typename F27, typename F28>
    requires std::is_invocable_r_v<T1, F1 &, unsigned int &> &&
             std::is_invocable_r_v<T1, F2 &, unsigned int &> &&
             std::is_invocable_r_v<T1, F3 &, unsigned int &> &&
             std::is_invocable_r_v<T1, F4 &, unsigned int &> &&
             std::is_invocable_r_v<T1, F5 &, unsigned int &> &&
             std::is_invocable_r_v<T1, F6 &, unsigned int &> &&
             std::is_invocable_r_v<T1, F20 &, unsigned int &> &&
             std::is_invocable_r_v<T1, F21 &, unsigned int &> &&
             std::is_invocable_r_v<T1, F22 &, unsigned int &, unsigned int &> &&
             std::is_invocable_r_v<T1, F23 &, unsigned int &, unsigned int &> &&
             std::is_invocable_r_v<T1, F24 &, unsigned int &> &&
             std::is_invocable_r_v<T1, F25 &, unsigned int &> &&
             std::is_invocable_r_v<T1, F26 &, unsigned int &> &&
             std::is_invocable_r_v<T1, F27 &, unsigned int &, unsigned int &> &&
             std::is_invocable_r_v<T1, F28 &, unsigned int &>
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
    requires std::is_invocable_r_v<T1, F1 &, unsigned int &> &&
             std::is_invocable_r_v<T1, F2 &, unsigned int &> &&
             std::is_invocable_r_v<T1, F3 &, unsigned int &> &&
             std::is_invocable_r_v<T1, F4 &, unsigned int &> &&
             std::is_invocable_r_v<T1, F5 &, unsigned int &> &&
             std::is_invocable_r_v<T1, F6 &, unsigned int &> &&
             std::is_invocable_r_v<T1, F20 &, unsigned int &> &&
             std::is_invocable_r_v<T1, F21 &, unsigned int &> &&
             std::is_invocable_r_v<T1, F22 &, unsigned int &, unsigned int &> &&
             std::is_invocable_r_v<T1, F23 &, unsigned int &, unsigned int &> &&
             std::is_invocable_r_v<T1, F24 &, unsigned int &> &&
             std::is_invocable_r_v<T1, F25 &, unsigned int &> &&
             std::is_invocable_r_v<T1, F26 &, unsigned int &> &&
             std::is_invocable_r_v<T1, F27 &, unsigned int &, unsigned int &> &&
             std::is_invocable_r_v<T1, F28 &, unsigned int &>
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
                                  7u,
                                  List<unsigned int>::cons(
                                      8u, List<unsigned int>::cons(
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
      false,
      10u,
      List<unsigned int>::cons(
          20u, List<unsigned int>::cons(30u, List<unsigned int>::nil())),
      42u,
      List<unsigned int>::cons(
          1u, List<unsigned int>::cons(
                  2u, List<unsigned int>::cons(
                          3u, List<unsigned int>::cons(
                                  4u, List<unsigned int>::nil()))))};
  static inline const unsigned int add_result =
      execute(sample, instr::add(4u)).ex_acc;
  static inline const unsigned int nop_acc =
      execute(sample, instr::nop()).ex_acc;
  static inline const unsigned int ldm_result =
      execute(sample, instr::ldm(5u)).ex_acc;
  static inline const unsigned int jun_pc =
      execute(sample, instr::jun(1024u)).ex_pc;
};

template <typename T1>
T1 ListDef::nth(unsigned int n, const List<T1> &l, T1 default0) {
  if (n <= 0) {
    if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
      return default0;
    } else {
      const auto &[a0, a1] = std::get<typename List<T1>::Cons>(l.v());
      return a0;
    }
  } else {
    unsigned int m = n - 1;
    if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
      return default0;
    } else {
      const auto &[a00, a10] = std::get<typename List<T1>::Cons>(l.v());
      return ListDef::template nth<T1>(m, *a10, default0);
    }
  }
}

#endif // INCLUDED_CPU_EMULATOR
