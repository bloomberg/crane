#ifndef INCLUDED_GET_PAIR_BOUND_PROP
#define INCLUDED_GET_PAIR_BOUND_PROP

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
  List clone() const {
    List _out{};

    struct _CloneFrame {
      const List *_src;
      List *_dst;
    };

    std::vector<_CloneFrame> _stack;
    _stack.push_back({this, &_out});
    while (!_stack.empty()) {
      auto _frame = _stack.back();
      _stack.pop_back();
      const List *_src = _frame._src;
      List *_dst = _frame._dst;
      if (std::holds_alternative<Nil>(_src->v())) {
        const auto &_alt = std::get<Nil>(_src->v());
        _dst->d_v_ = Nil{};
      } else {
        const auto &_alt = std::get<Cons>(_src->v());
        _dst->d_v_ =
            Cons{_alt.d_a0, _alt.d_a1 ? std::make_unique<List>() : nullptr};
        auto &_dst_alt = std::get<Cons>(_dst->d_v_);
        if (_alt.d_a1)
          _stack.push_back({_alt.d_a1.get(), _dst_alt.d_a1.get()});
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
    std::vector<std::unique_ptr<List>> _stack;
    auto _drain = [&](List &_node) {
      if (std::holds_alternative<Cons>(_node.d_v_)) {
        auto &_alt = std::get<Cons>(_node.d_v_);
        if (_alt.d_a1)
          _stack.push_back(std::move(_alt.d_a1));
      }
    };
    _drain(*this);
    while (!_stack.empty()) {
      auto _node = std::move(_stack.back());
      _stack.pop_back();
      if (_node)
        _drain(*_node);
    }
  }

  inline variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  const variant_t &v() const { return d_v_; }

  List<t_A> skipn(const unsigned int &n) const {
    if (n <= 0) {
      return std::move(*(this));
    } else {
      unsigned int n0 = n - 1;
      auto &&_sv = *(this);
      if (std::holds_alternative<typename List<t_A>::Nil>(_sv.v())) {
        return List<t_A>::nil();
      } else {
        auto &[d_a0, d_a1] = std::get<typename List<t_A>::Cons>(_sv.v());
        return (*(d_a1)).skipn(n0);
      }
    }
  }

  List<t_A> firstn(const unsigned int &n) const {
    if (n <= 0) {
      return List<t_A>::nil();
    } else {
      unsigned int n0 = n - 1;
      auto &&_sv = *(this);
      if (std::holds_alternative<typename List<t_A>::Nil>(_sv.v())) {
        return List<t_A>::nil();
      } else {
        const auto &[d_a0, d_a1] = std::get<typename List<t_A>::Cons>(_sv.v());
        return List<t_A>::cons(d_a0, (*(d_a1)).firstn(n0));
      }
    }
  }
};

struct ListDef {
  template <typename T1>
  static T1 nth(const unsigned int &n, const List<T1> &l, const T1 default0);
};

struct GetPairBoundProp {
  template <typename T1>
  static List<T1> update_nth(const unsigned int &n, const T1 x,
                             const List<T1> &l) {
    if (n <= 0) {
      if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
        return List<T1>::nil();
      } else {
        const auto &[d_a0, d_a1] = std::get<typename List<T1>::Cons>(l.v());
        return List<T1>::cons(x, *(d_a1));
      }
    } else {
      unsigned int n_ = n - 1;
      if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
        return List<T1>::nil();
      } else {
        const auto &[d_a00, d_a10] = std::get<typename List<T1>::Cons>(l.v());
        return List<T1>::cons(d_a00, update_nth<T1>(n_, x, *(d_a10)));
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
      return state{(*(this)).ex_acc,           (*(this)).ex_regs.clone(),
                   (*(this)).ex_carry,         (*(this)).ex_pc,
                   (*(this)).ex_stack.clone(), (*(this)).ex_pair_bus,
                   (*(this)).ex_ports.clone()};
    }
  };

  static unsigned int get_reg(const state &s, const unsigned int &r);
  static List<unsigned int> set_reg(const state &s, const unsigned int &r,
                                    const unsigned int &v);
  static unsigned int pair_base(const unsigned int &r);
  static unsigned int get_pair(const state &s, const unsigned int &r);
  static List<unsigned int> set_pair(const state &s, const unsigned int &r,
                                     const unsigned int &v);
  static List<unsigned int> push_return(const state &s,
                                        const unsigned int &ret);

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
    instr() {}

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

    instr(const instr &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    instr(instr &&_other) : d_v_(std::move(_other.d_v_)) {}

    instr &operator=(const instr &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    instr &operator=(instr &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    instr clone() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<NOP>(_sv.v())) {
        return instr(NOP{});
      } else if (std::holds_alternative<LDM>(_sv.v())) {
        const auto &[d_n] = std::get<LDM>(_sv.v());
        return instr(LDM{d_n});
      } else if (std::holds_alternative<LD>(_sv.v())) {
        const auto &[d_r] = std::get<LD>(_sv.v());
        return instr(LD{d_r});
      } else if (std::holds_alternative<XCH>(_sv.v())) {
        const auto &[d_r] = std::get<XCH>(_sv.v());
        return instr(XCH{d_r});
      } else if (std::holds_alternative<INC>(_sv.v())) {
        const auto &[d_r] = std::get<INC>(_sv.v());
        return instr(INC{d_r});
      } else if (std::holds_alternative<ADD>(_sv.v())) {
        const auto &[d_r] = std::get<ADD>(_sv.v());
        return instr(ADD{d_r});
      } else if (std::holds_alternative<SUB>(_sv.v())) {
        const auto &[d_r] = std::get<SUB>(_sv.v());
        return instr(SUB{d_r});
      } else if (std::holds_alternative<IAC>(_sv.v())) {
        return instr(IAC{});
      } else if (std::holds_alternative<DAC>(_sv.v())) {
        return instr(DAC{});
      } else if (std::holds_alternative<CLC>(_sv.v())) {
        return instr(CLC{});
      } else if (std::holds_alternative<STC>(_sv.v())) {
        return instr(STC{});
      } else if (std::holds_alternative<CMC>(_sv.v())) {
        return instr(CMC{});
      } else if (std::holds_alternative<CMA>(_sv.v())) {
        return instr(CMA{});
      } else if (std::holds_alternative<CLB>(_sv.v())) {
        return instr(CLB{});
      } else if (std::holds_alternative<RAL>(_sv.v())) {
        return instr(RAL{});
      } else if (std::holds_alternative<RAR>(_sv.v())) {
        return instr(RAR{});
      } else if (std::holds_alternative<TCC>(_sv.v())) {
        return instr(TCC{});
      } else if (std::holds_alternative<TCS>(_sv.v())) {
        return instr(TCS{});
      } else if (std::holds_alternative<DAA>(_sv.v())) {
        return instr(DAA{});
      } else if (std::holds_alternative<KBP>(_sv.v())) {
        return instr(KBP{});
      } else if (std::holds_alternative<JUN>(_sv.v())) {
        const auto &[d_a] = std::get<JUN>(_sv.v());
        return instr(JUN{d_a});
      } else if (std::holds_alternative<JMS>(_sv.v())) {
        const auto &[d_a] = std::get<JMS>(_sv.v());
        return instr(JMS{d_a});
      } else if (std::holds_alternative<JCN>(_sv.v())) {
        const auto &[d_c, d_a] = std::get<JCN>(_sv.v());
        return instr(JCN{d_c, d_a});
      } else if (std::holds_alternative<FIM>(_sv.v())) {
        const auto &[d_r, d_d] = std::get<FIM>(_sv.v());
        return instr(FIM{d_r, d_d});
      } else if (std::holds_alternative<SRC>(_sv.v())) {
        const auto &[d_r] = std::get<SRC>(_sv.v());
        return instr(SRC{d_r});
      } else if (std::holds_alternative<FIN>(_sv.v())) {
        const auto &[d_r] = std::get<FIN>(_sv.v());
        return instr(FIN{d_r});
      } else if (std::holds_alternative<JIN>(_sv.v())) {
        const auto &[d_r] = std::get<JIN>(_sv.v());
        return instr(JIN{d_r});
      } else if (std::holds_alternative<ISZ>(_sv.v())) {
        const auto &[d_r, d_a] = std::get<ISZ>(_sv.v());
        return instr(ISZ{d_r, d_a});
      } else {
        const auto &[d_d] = std::get<BBL>(_sv.v());
        return instr(BBL{d_d});
      }
    }

    // CREATORS
    static instr nop() { return instr(NOP{}); }

    static instr ldm(unsigned int n) { return instr(LDM{std::move(n)}); }

    static instr ld(unsigned int r) { return instr(LD{std::move(r)}); }

    static instr xch(unsigned int r) { return instr(XCH{std::move(r)}); }

    static instr inc(unsigned int r) { return instr(INC{std::move(r)}); }

    static instr add(unsigned int r) { return instr(ADD{std::move(r)}); }

    static instr sub(unsigned int r) { return instr(SUB{std::move(r)}); }

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

    static instr jun(unsigned int a) { return instr(JUN{std::move(a)}); }

    static instr jms(unsigned int a) { return instr(JMS{std::move(a)}); }

    static instr jcn(unsigned int c, unsigned int a) {
      return instr(JCN{std::move(c), std::move(a)});
    }

    static instr fim(unsigned int r, unsigned int d) {
      return instr(FIM{std::move(r), std::move(d)});
    }

    static instr src(unsigned int r) { return instr(SRC{std::move(r)}); }

    static instr fin(unsigned int r) { return instr(FIN{std::move(r)}); }

    static instr jin(unsigned int r) { return instr(JIN{std::move(r)}); }

    static instr isz(unsigned int r, unsigned int a) {
      return instr(ISZ{std::move(r), std::move(a)});
    }

    static instr bbl(unsigned int d) { return instr(BBL{std::move(d)}); }

    // MANIPULATORS
    inline variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    const variant_t &v() const { return d_v_; }
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
                       F27 &&f26, F28 &&f27, const instr &i) {
    if (std::holds_alternative<typename instr::NOP>(i.v())) {
      return f;
    } else if (std::holds_alternative<typename instr::LDM>(i.v())) {
      const auto &[d_n] = std::get<typename instr::LDM>(i.v());
      return f0(d_n);
    } else if (std::holds_alternative<typename instr::LD>(i.v())) {
      const auto &[d_r] = std::get<typename instr::LD>(i.v());
      return f1(d_r);
    } else if (std::holds_alternative<typename instr::XCH>(i.v())) {
      const auto &[d_r] = std::get<typename instr::XCH>(i.v());
      return f2(d_r);
    } else if (std::holds_alternative<typename instr::INC>(i.v())) {
      const auto &[d_r] = std::get<typename instr::INC>(i.v());
      return f3(d_r);
    } else if (std::holds_alternative<typename instr::ADD>(i.v())) {
      const auto &[d_r] = std::get<typename instr::ADD>(i.v());
      return f4(d_r);
    } else if (std::holds_alternative<typename instr::SUB>(i.v())) {
      const auto &[d_r] = std::get<typename instr::SUB>(i.v());
      return f5(d_r);
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
      const auto &[d_a] = std::get<typename instr::JUN>(i.v());
      return f19(d_a);
    } else if (std::holds_alternative<typename instr::JMS>(i.v())) {
      const auto &[d_a] = std::get<typename instr::JMS>(i.v());
      return f20(d_a);
    } else if (std::holds_alternative<typename instr::JCN>(i.v())) {
      const auto &[d_c, d_a] = std::get<typename instr::JCN>(i.v());
      return f21(d_c, d_a);
    } else if (std::holds_alternative<typename instr::FIM>(i.v())) {
      const auto &[d_r, d_d] = std::get<typename instr::FIM>(i.v());
      return f22(d_r, d_d);
    } else if (std::holds_alternative<typename instr::SRC>(i.v())) {
      const auto &[d_r] = std::get<typename instr::SRC>(i.v());
      return f23(d_r);
    } else if (std::holds_alternative<typename instr::FIN>(i.v())) {
      const auto &[d_r] = std::get<typename instr::FIN>(i.v());
      return f24(d_r);
    } else if (std::holds_alternative<typename instr::JIN>(i.v())) {
      const auto &[d_r] = std::get<typename instr::JIN>(i.v());
      return f25(d_r);
    } else if (std::holds_alternative<typename instr::ISZ>(i.v())) {
      const auto &[d_r, d_a] = std::get<typename instr::ISZ>(i.v());
      return f26(d_r, d_a);
    } else {
      const auto &[d_d] = std::get<typename instr::BBL>(i.v());
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
                      F27 &&f26, F28 &&f27, const instr &i) {
    if (std::holds_alternative<typename instr::NOP>(i.v())) {
      return f;
    } else if (std::holds_alternative<typename instr::LDM>(i.v())) {
      const auto &[d_n] = std::get<typename instr::LDM>(i.v());
      return f0(d_n);
    } else if (std::holds_alternative<typename instr::LD>(i.v())) {
      const auto &[d_r] = std::get<typename instr::LD>(i.v());
      return f1(d_r);
    } else if (std::holds_alternative<typename instr::XCH>(i.v())) {
      const auto &[d_r] = std::get<typename instr::XCH>(i.v());
      return f2(d_r);
    } else if (std::holds_alternative<typename instr::INC>(i.v())) {
      const auto &[d_r] = std::get<typename instr::INC>(i.v());
      return f3(d_r);
    } else if (std::holds_alternative<typename instr::ADD>(i.v())) {
      const auto &[d_r] = std::get<typename instr::ADD>(i.v());
      return f4(d_r);
    } else if (std::holds_alternative<typename instr::SUB>(i.v())) {
      const auto &[d_r] = std::get<typename instr::SUB>(i.v());
      return f5(d_r);
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
      const auto &[d_a] = std::get<typename instr::JUN>(i.v());
      return f19(d_a);
    } else if (std::holds_alternative<typename instr::JMS>(i.v())) {
      const auto &[d_a] = std::get<typename instr::JMS>(i.v());
      return f20(d_a);
    } else if (std::holds_alternative<typename instr::JCN>(i.v())) {
      const auto &[d_c, d_a] = std::get<typename instr::JCN>(i.v());
      return f21(d_c, d_a);
    } else if (std::holds_alternative<typename instr::FIM>(i.v())) {
      const auto &[d_r, d_d] = std::get<typename instr::FIM>(i.v());
      return f22(d_r, d_d);
    } else if (std::holds_alternative<typename instr::SRC>(i.v())) {
      const auto &[d_r] = std::get<typename instr::SRC>(i.v());
      return f23(d_r);
    } else if (std::holds_alternative<typename instr::FIN>(i.v())) {
      const auto &[d_r] = std::get<typename instr::FIN>(i.v());
      return f24(d_r);
    } else if (std::holds_alternative<typename instr::JIN>(i.v())) {
      const auto &[d_r] = std::get<typename instr::JIN>(i.v());
      return f25(d_r);
    } else if (std::holds_alternative<typename instr::ISZ>(i.v())) {
      const auto &[d_r, d_a] = std::get<typename instr::ISZ>(i.v());
      return f26(d_r, d_a);
    } else {
      const auto &[d_d] = std::get<typename instr::BBL>(i.v());
      return f27(d_d);
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
};

template <typename T1>
T1 ListDef::nth(const unsigned int &n, const List<T1> &l, const T1 default0) {
  if (n <= 0) {
    if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
      return default0;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<T1>::Cons>(l.v());
      return d_a0;
    }
  } else {
    unsigned int m = n - 1;
    if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
      return default0;
    } else {
      const auto &[d_a00, d_a10] = std::get<typename List<T1>::Cons>(l.v());
      return ListDef::template nth<T1>(m, *(d_a10), default0);
    }
  }
}

#endif // INCLUDED_GET_PAIR_BOUND_PROP
