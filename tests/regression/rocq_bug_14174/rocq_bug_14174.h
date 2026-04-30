#ifndef INCLUDED_ROCQ_BUG_14174
#define INCLUDED_ROCQ_BUG_14174

#include <any>
#include <functional>
#include <memory>
#include <optional>
#include <stdexcept>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

enum class Bool0 { e_TRUE0, e_FALSE0 };

struct Nat {
  // TYPES
  struct O {};

  struct S {
    std::unique_ptr<Nat> d_a0;
  };

  using variant_t = std::variant<O, S>;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  Nat() {}

  explicit Nat(O _v) : d_v_(_v) {}

  explicit Nat(S _v) : d_v_(std::move(_v)) {}

  Nat(const Nat &_other) : d_v_(std::move(_other.clone().d_v_)) {}

  Nat(Nat &&_other) : d_v_(std::move(_other.d_v_)) {}

  Nat &operator=(const Nat &_other) {
    d_v_ = std::move(_other.clone().d_v_);
    return *this;
  }

  Nat &operator=(Nat &&_other) {
    d_v_ = std::move(_other.d_v_);
    return *this;
  }

  // ACCESSORS
  Nat clone() const {
    Nat _out{};

    struct _CloneFrame {
      const Nat *_src;
      Nat *_dst;
    };

    std::vector<_CloneFrame> _stack{};
    _stack.push_back({this, &_out});
    while (!_stack.empty()) {
      auto _frame = _stack.back();
      _stack.pop_back();
      const Nat *_src = _frame._src;
      Nat *_dst = _frame._dst;
      if (std::holds_alternative<O>(_src->v())) {
        _dst->d_v_ = O{};
      } else {
        const auto &_alt = std::get<S>(_src->v());
        _dst->d_v_ = S{_alt.d_a0 ? std::make_unique<Nat>() : nullptr};
        auto &_dst_alt = std::get<S>(_dst->d_v_);
        if (_alt.d_a0) {
          _stack.push_back({_alt.d_a0.get(), _dst_alt.d_a0.get()});
        }
      }
    }
    return _out;
  }

  // CREATORS
  static Nat o() { return Nat(O{}); }

  static Nat s(Nat a0) { return Nat(S{std::make_unique<Nat>(std::move(a0))}); }

  // MANIPULATORS
  ~Nat() {
    std::vector<std::unique_ptr<Nat>> _stack{};
    auto _drain = [&](Nat &_node) {
      if (std::holds_alternative<S>(_node.d_v_)) {
        auto &_alt = std::get<S>(_node.d_v_);
        if (_alt.d_a0) {
          _stack.push_back(std::move(_alt.d_a0));
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

template <typename t_A> struct Option {
  // TYPES
  struct Some {
    t_A d_a0;
  };

  struct None {};

  using variant_t = std::variant<Some, None>;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  Option() {}

  explicit Option(Some _v) : d_v_(std::move(_v)) {}

  explicit Option(None _v) : d_v_(_v) {}

  Option(const Option<t_A> &_other) : d_v_(std::move(_other.clone().d_v_)) {}

  Option(Option<t_A> &&_other) : d_v_(std::move(_other.d_v_)) {}

  Option<t_A> &operator=(const Option<t_A> &_other) {
    d_v_ = std::move(_other.clone().d_v_);
    return *this;
  }

  Option<t_A> &operator=(Option<t_A> &&_other) {
    d_v_ = std::move(_other.d_v_);
    return *this;
  }

  // ACCESSORS
  Option<t_A> clone() const {
    auto &&_sv = *(this);
    if (std::holds_alternative<Some>(_sv.v())) {
      const auto &[d_a0] = std::get<Some>(_sv.v());
      return Option<t_A>(Some{d_a0});
    } else {
      return Option<t_A>(None{});
    }
  }

  // CREATORS
  template <typename _U> explicit Option(const Option<_U> &_other) {
    if (std::holds_alternative<typename Option<_U>::Some>(_other.v())) {
      const auto &[d_a0] = std::get<typename Option<_U>::Some>(_other.v());
      d_v_ = Some{t_A(d_a0)};
    } else {
      d_v_ = None{};
    }
  }

  static Option<t_A> some(t_A a0) { return Option(Some{std::move(a0)}); }

  static Option<t_A> none() { return Option(None{}); }

  // MANIPULATORS
  inline variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  const variant_t &v() const { return d_v_; }
};

template <typename t_A, typename t_B> struct Prod {
  // TYPES
  struct Pair {
    t_A d_a0;
    t_B d_a1;
  };

  using variant_t = std::variant<Pair>;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  Prod() {}

  explicit Prod(Pair _v) : d_v_(std::move(_v)) {}

  Prod(const Prod<t_A, t_B> &_other) : d_v_(std::move(_other.clone().d_v_)) {}

  Prod(Prod<t_A, t_B> &&_other) : d_v_(std::move(_other.d_v_)) {}

  Prod<t_A, t_B> &operator=(const Prod<t_A, t_B> &_other) {
    d_v_ = std::move(_other.clone().d_v_);
    return *this;
  }

  Prod<t_A, t_B> &operator=(Prod<t_A, t_B> &&_other) {
    d_v_ = std::move(_other.d_v_);
    return *this;
  }

  // ACCESSORS
  Prod<t_A, t_B> clone() const {
    auto &&_sv = *(this);
    const auto &[d_a0, d_a1] = std::get<Pair>(_sv.v());
    return Prod<t_A, t_B>(Pair{d_a0, d_a1});
  }

  // CREATORS
  template <typename _U0, typename _U1>
  explicit Prod(const Prod<_U0, _U1> &_other) {
    const auto &[d_a0, d_a1] =
        std::get<typename Prod<_U0, _U1>::Pair>(_other.v());
    d_v_ = Pair{t_A(d_a0), t_B(d_a1)};
  }

  static Prod<t_A, t_B> pair(t_A a0, t_B a1) {
    return Prod(Pair{std::move(a0), std::move(a1)});
  }

  // MANIPULATORS
  inline variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  const variant_t &v() const { return d_v_; }

  t_A fst() const {
    auto &&_sv = *(this);
    const auto &[d_a0, d_a1] = std::get<typename Prod<t_A, t_B>::Pair>(_sv.v());
    return d_a0;
  }

  t_B snd() const {
    auto &&_sv = *(this);
    const auto &[d_a0, d_a1] = std::get<typename Prod<t_A, t_B>::Pair>(_sv.v());
    return d_a1;
  }
};

template <typename t_A> struct Sig {
  // TYPES
  struct Exist0 {
    t_A d_x;
  };

  using variant_t = std::variant<Exist0>;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  Sig() {}

  explicit Sig(Exist0 _v) : d_v_(std::move(_v)) {}

  Sig(const Sig<t_A> &_other) : d_v_(std::move(_other.clone().d_v_)) {}

  Sig(Sig<t_A> &&_other) : d_v_(std::move(_other.d_v_)) {}

  Sig<t_A> &operator=(const Sig<t_A> &_other) {
    d_v_ = std::move(_other.clone().d_v_);
    return *this;
  }

  Sig<t_A> &operator=(Sig<t_A> &&_other) {
    d_v_ = std::move(_other.d_v_);
    return *this;
  }

  // ACCESSORS
  Sig<t_A> clone() const {
    auto &&_sv = *(this);
    const auto &[d_x] = std::get<Exist0>(_sv.v());
    return Sig<t_A>(Exist0{d_x});
  }

  // CREATORS
  template <typename _U> explicit Sig(const Sig<_U> &_other) {
    const auto &[d_x] = std::get<typename Sig<_U>::Exist0>(_other.v());
    d_v_ = Exist0{t_A(d_x)};
  }

  static Sig<t_A> exist0(t_A x) { return Sig(Exist0{std::move(x)}); }

  // MANIPULATORS
  inline variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  const variant_t &v() const { return d_v_; }
};

template <typename t_A> struct Sig2 {
  // TYPES
  struct Exist1 {
    t_A d_x;
  };

  using variant_t = std::variant<Exist1>;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  Sig2() {}

  explicit Sig2(Exist1 _v) : d_v_(std::move(_v)) {}

  Sig2(const Sig2<t_A> &_other) : d_v_(std::move(_other.clone().d_v_)) {}

  Sig2(Sig2<t_A> &&_other) : d_v_(std::move(_other.d_v_)) {}

  Sig2<t_A> &operator=(const Sig2<t_A> &_other) {
    d_v_ = std::move(_other.clone().d_v_);
    return *this;
  }

  Sig2<t_A> &operator=(Sig2<t_A> &&_other) {
    d_v_ = std::move(_other.d_v_);
    return *this;
  }

  // ACCESSORS
  Sig2<t_A> clone() const {
    auto &&_sv = *(this);
    const auto &[d_x] = std::get<Exist1>(_sv.v());
    return Sig2<t_A>(Exist1{d_x});
  }

  // CREATORS
  template <typename _U> explicit Sig2(const Sig2<_U> &_other) {
    const auto &[d_x] = std::get<typename Sig2<_U>::Exist1>(_other.v());
    d_v_ = Exist1{t_A(d_x)};
  }

  static Sig2<t_A> exist1(t_A x) { return Sig2(Exist1{std::move(x)}); }

  // MANIPULATORS
  inline variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  const variant_t &v() const { return d_v_; }
};

template <typename t_A, typename t_P> struct SigT {
  // TYPES
  struct ExistT0 {
    t_A d_x;
    t_P d_a1;
  };

  using variant_t = std::variant<ExistT0>;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  SigT() {}

  explicit SigT(ExistT0 _v) : d_v_(std::move(_v)) {}

  SigT(const SigT<t_A, t_P> &_other) : d_v_(std::move(_other.clone().d_v_)) {}

  SigT(SigT<t_A, t_P> &&_other) : d_v_(std::move(_other.d_v_)) {}

  SigT<t_A, t_P> &operator=(const SigT<t_A, t_P> &_other) {
    d_v_ = std::move(_other.clone().d_v_);
    return *this;
  }

  SigT<t_A, t_P> &operator=(SigT<t_A, t_P> &&_other) {
    d_v_ = std::move(_other.d_v_);
    return *this;
  }

  // ACCESSORS
  SigT<t_A, t_P> clone() const {
    auto &&_sv = *(this);
    const auto &[d_x, d_a1] = std::get<ExistT0>(_sv.v());
    return SigT<t_A, t_P>(ExistT0{d_x, d_a1});
  }

  // CREATORS
  template <typename _U0, typename _U1>
  explicit SigT(const SigT<_U0, _U1> &_other) {
    const auto &[d_x, d_a1] =
        std::get<typename SigT<_U0, _U1>::ExistT0>(_other.v());
    d_v_ = ExistT0{t_A(d_x), t_P(d_a1)};
  }

  static SigT<t_A, t_P> existt0(t_A x, t_P a1) {
    return SigT(ExistT0{std::move(x), std::move(a1)});
  }

  // MANIPULATORS
  inline variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  const variant_t &v() const { return d_v_; }
};

template <typename t_A, typename t_P, typename t_Q> struct SigT2 {
  // TYPES
  struct ExistT1 {
    t_A d_x;
    t_P d_a1;
    t_Q d_a2;
  };

  using variant_t = std::variant<ExistT1>;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  SigT2() {}

  explicit SigT2(ExistT1 _v) : d_v_(std::move(_v)) {}

  SigT2(const SigT2<t_A, t_P, t_Q> &_other)
      : d_v_(std::move(_other.clone().d_v_)) {}

  SigT2(SigT2<t_A, t_P, t_Q> &&_other) : d_v_(std::move(_other.d_v_)) {}

  SigT2<t_A, t_P, t_Q> &operator=(const SigT2<t_A, t_P, t_Q> &_other) {
    d_v_ = std::move(_other.clone().d_v_);
    return *this;
  }

  SigT2<t_A, t_P, t_Q> &operator=(SigT2<t_A, t_P, t_Q> &&_other) {
    d_v_ = std::move(_other.d_v_);
    return *this;
  }

  // ACCESSORS
  SigT2<t_A, t_P, t_Q> clone() const {
    auto &&_sv = *(this);
    const auto &[d_x, d_a1, d_a2] = std::get<ExistT1>(_sv.v());
    return SigT2<t_A, t_P, t_Q>(ExistT1{d_x, d_a1, d_a2});
  }

  // CREATORS
  template <typename _U0, typename _U1, typename _U2>
  explicit SigT2(const SigT2<_U0, _U1, _U2> &_other) {
    const auto &[d_x, d_a1, d_a2] =
        std::get<typename SigT2<_U0, _U1, _U2>::ExistT1>(_other.v());
    d_v_ = ExistT1{t_A(d_x), t_P(d_a1), t_Q(d_a2)};
  }

  static SigT2<t_A, t_P, t_Q> existt1(t_A x, t_P a1, t_Q a2) {
    return SigT2(ExistT1{std::move(x), std::move(a1), std::move(a2)});
  }

  // MANIPULATORS
  inline variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  const variant_t &v() const { return d_v_; }
};

struct SigTNotations {};
enum class Sumbool { e_LEFT0, e_RIGHT0 };

template <typename t_A> struct Sumor {
  // TYPES
  struct Inleft {
    t_A d_a0;
  };

  struct Inright {};

  using variant_t = std::variant<Inleft, Inright>;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  Sumor() {}

  explicit Sumor(Inleft _v) : d_v_(std::move(_v)) {}

  explicit Sumor(Inright _v) : d_v_(_v) {}

  Sumor(const Sumor<t_A> &_other) : d_v_(std::move(_other.clone().d_v_)) {}

  Sumor(Sumor<t_A> &&_other) : d_v_(std::move(_other.d_v_)) {}

  Sumor<t_A> &operator=(const Sumor<t_A> &_other) {
    d_v_ = std::move(_other.clone().d_v_);
    return *this;
  }

  Sumor<t_A> &operator=(Sumor<t_A> &&_other) {
    d_v_ = std::move(_other.d_v_);
    return *this;
  }

  // ACCESSORS
  Sumor<t_A> clone() const {
    auto &&_sv = *(this);
    if (std::holds_alternative<Inleft>(_sv.v())) {
      const auto &[d_a0] = std::get<Inleft>(_sv.v());
      return Sumor<t_A>(Inleft{d_a0});
    } else {
      return Sumor<t_A>(Inright{});
    }
  }

  // CREATORS
  template <typename _U> explicit Sumor(const Sumor<_U> &_other) {
    if (std::holds_alternative<typename Sumor<_U>::Inleft>(_other.v())) {
      const auto &[d_a0] = std::get<typename Sumor<_U>::Inleft>(_other.v());
      d_v_ = Inleft{t_A(d_a0)};
    } else {
      d_v_ = Inright{};
    }
  }

  static Sumor<t_A> inleft(t_A a0) { return Sumor(Inleft{std::move(a0)}); }

  static Sumor<t_A> inright() { return Sumor(Inright{}); }

  // MANIPULATORS
  inline variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  const variant_t &v() const { return d_v_; }
};

struct RocqBug14174 {
  struct A {
    template <typename t_A> struct sig {
      // TYPES
      struct Exist {
        t_A d_x;
      };

      using variant_t = std::variant<Exist>;

    private:
      // DATA
      variant_t d_v_;

    public:
      // CREATORS
      sig() {}

      explicit sig(Exist _v) : d_v_(std::move(_v)) {}

      sig(const sig<t_A> &_other) : d_v_(std::move(_other.clone().d_v_)) {}

      sig(sig<t_A> &&_other) : d_v_(std::move(_other.d_v_)) {}

      sig<t_A> &operator=(const sig<t_A> &_other) {
        d_v_ = std::move(_other.clone().d_v_);
        return *this;
      }

      sig<t_A> &operator=(sig<t_A> &&_other) {
        d_v_ = std::move(_other.d_v_);
        return *this;
      }

      // ACCESSORS
      sig<t_A> clone() const {
        auto &&_sv = *(this);
        const auto &[d_x] = std::get<Exist>(_sv.v());
        return sig<t_A>(Exist{d_x});
      }

      // CREATORS
      template <typename _U> explicit sig(const sig<_U> &_other) {
        const auto &[d_x] = std::get<typename sig<_U>::Exist>(_other.v());
        d_v_ = Exist{t_A(d_x)};
      }

      static sig<t_A> exist(t_A x) { return sig(Exist{std::move(x)}); }

      // MANIPULATORS
      inline variant_t &v_mut() { return d_v_; }

      // ACCESSORS
      const variant_t &v() const { return d_v_; }

      template <typename T1> T1 eq_sig_rec_uncurried() const {
        return this->eq_sig_rect_uncurried();
      }

      template <typename T1>
      T1 eq_sig_rect_uncurried(const sig<t_A> &v, const T1 f) const {
        return (*(this)).eq_sig_rect(v, [=]() mutable { return f; }());
      }

      template <typename T1>
      T1 eq_sig_rect_exist_r(const t_A v1, const T1 f) const {
        return (*(this)).eq_sig_rect(sig<t_A>::exist(v1), f);
      }

      template <typename T1>
      T1 eq_sig_rect_exist_l(const t_A u1, const T1 f) const {
        return sig<t_A>::exist(u1).eq_sig_rect(*(this), f);
      }

      template <typename T1> T1 eq_sig_rec() const {
        return this->eq_sig_rect();
      }

      template <typename T1>
      T1 eq_sig_rect(const sig<t_A> &, const T1 f) const {
        return f;
      }

      t_A proj1_sig() const {
        auto &&_sv = *(this);
        const auto &[d_x] = std::get<typename sig<t_A>::Exist>(_sv.v());
        return d_x;
      }

      template <typename T1, MapsTo<T1, t_A> F0> T1 sig_rec(F0 &&f) const {
        auto &&_sv = *(this);
        const auto &[d_x] = std::get<typename sig<t_A>::Exist>(_sv.v());
        return f(d_x);
      }

      template <typename T1, MapsTo<T1, t_A> F0> T1 sig_rect(F0 &&f) const {
        auto &&_sv = *(this);
        const auto &[d_x] = std::get<typename sig<t_A>::Exist>(_sv.v());
        return f(d_x);
      }
    };

    template <typename t_A> struct sig2 {
      // TYPES
      struct Exist2 {
        t_A d_x;
      };

      using variant_t = std::variant<Exist2>;

    private:
      // DATA
      variant_t d_v_;

    public:
      // CREATORS
      sig2() {}

      explicit sig2(Exist2 _v) : d_v_(std::move(_v)) {}

      sig2(const sig2<t_A> &_other) : d_v_(std::move(_other.clone().d_v_)) {}

      sig2(sig2<t_A> &&_other) : d_v_(std::move(_other.d_v_)) {}

      sig2<t_A> &operator=(const sig2<t_A> &_other) {
        d_v_ = std::move(_other.clone().d_v_);
        return *this;
      }

      sig2<t_A> &operator=(sig2<t_A> &&_other) {
        d_v_ = std::move(_other.d_v_);
        return *this;
      }

      // ACCESSORS
      sig2<t_A> clone() const {
        auto &&_sv = *(this);
        const auto &[d_x] = std::get<Exist2>(_sv.v());
        return sig2<t_A>(Exist2{d_x});
      }

      // CREATORS
      template <typename _U> explicit sig2(const sig2<_U> &_other) {
        const auto &[d_x] = std::get<typename sig2<_U>::Exist2>(_other.v());
        d_v_ = Exist2{t_A(d_x)};
      }

      static sig2<t_A> exist2(t_A x) { return sig2(Exist2{std::move(x)}); }

      // MANIPULATORS
      inline variant_t &v_mut() { return d_v_; }

      // ACCESSORS
      const variant_t &v() const { return d_v_; }

      template <typename T1> T1 eq_sig2_rec_uncurried() const {
        return this->eq_sig2_rect_uncurried();
      }

      template <typename T1>
      T1 eq_sig2_rect_uncurried(const sig2<t_A> &v, const T1 f) const {
        return (*(this)).eq_sig2_rect(v, [=]() mutable { return f; }());
      }

      template <typename T1>
      T1 eq_sig2_rect_exist2_r(const t_A v1, const T1 f) const {
        return (*(this)).eq_sig2_rect(sig2<t_A>::exist2(v1), f);
      }

      template <typename T1>
      T1 eq_sig2_rect_exist2_l(const t_A u1, const T1 f) const {
        return sig2<t_A>::exist2(u1).eq_sig2_rect(*(this), f);
      }

      template <typename T1> T1 eq_sig2_rec() const {
        return this->eq_sig2_rect();
      }

      template <typename T1>
      T1 eq_sig2_rect(const sig2<t_A> &, const T1 f) const {
        return f;
      }

      sig<t_A> sig_of_sig2() const {
        sig2<t_A> _self = *(this);
        return sig<t_A>::exist([=]() mutable {
          const auto &[d_x] = std::get<typename sig2<t_A>::Exist2>(_self.v());
          return d_x;
        }());
      }

      template <typename T1, MapsTo<T1, t_A> F0> T1 sig2_rec(F0 &&f) const {
        auto &&_sv = *(this);
        const auto &[d_x] = std::get<typename sig2<t_A>::Exist2>(_sv.v());
        return f(d_x);
      }

      template <typename T1, MapsTo<T1, t_A> F0> T1 sig2_rect(F0 &&f) const {
        auto &&_sv = *(this);
        const auto &[d_x] = std::get<typename sig2<t_A>::Exist2>(_sv.v());
        return f(d_x);
      }
    };

    template <typename t_A, typename t_P> struct sigT {
      // TYPES
      struct ExistT {
        t_A d_x;
        t_P d_a1;
      };

      using variant_t = std::variant<ExistT>;

    private:
      // DATA
      variant_t d_v_;

    public:
      // CREATORS
      sigT() {}

      explicit sigT(ExistT _v) : d_v_(std::move(_v)) {}

      sigT(const sigT<t_A, t_P> &_other)
          : d_v_(std::move(_other.clone().d_v_)) {}

      sigT(sigT<t_A, t_P> &&_other) : d_v_(std::move(_other.d_v_)) {}

      sigT<t_A, t_P> &operator=(const sigT<t_A, t_P> &_other) {
        d_v_ = std::move(_other.clone().d_v_);
        return *this;
      }

      sigT<t_A, t_P> &operator=(sigT<t_A, t_P> &&_other) {
        d_v_ = std::move(_other.d_v_);
        return *this;
      }

      // ACCESSORS
      sigT<t_A, t_P> clone() const {
        auto &&_sv = *(this);
        const auto &[d_x, d_a1] = std::get<ExistT>(_sv.v());
        return sigT<t_A, t_P>(ExistT{d_x, d_a1});
      }

      // CREATORS
      template <typename _U0, typename _U1>
      explicit sigT(const sigT<_U0, _U1> &_other) {
        const auto &[d_x, d_a1] =
            std::get<typename sigT<_U0, _U1>::ExistT>(_other.v());
        d_v_ = ExistT{t_A(d_x), t_P(d_a1)};
      }

      static sigT<t_A, t_P> existt(t_A x, t_P a1) {
        return sigT(ExistT{std::move(x), std::move(a1)});
      }

      // MANIPULATORS
      inline variant_t &v_mut() { return d_v_; }

      // ACCESSORS
      const variant_t &v() const { return d_v_; }

      template <typename T1> T1 eq_sigT_rec_uncurried() const {
        return this->eq_sigT_rect_uncurried();
      }

      template <typename T1>
      T1 eq_sigT_rect_uncurried(const sigT<t_A, t_P> &v, const T1 f) const {
        return (*(this)).eq_sigT_rect(v, [=]() mutable { return f; }());
      }

      template <typename T1>
      T1 eq_sigT_rect_existT_r(const t_A v1, const t_P v2, const T1 f) const {
        return (*(this)).eq_sigT_rect(sigT<t_A, t_P>::existt(v1, v2), f);
      }

      template <typename T1>
      T1 eq_sigT_rect_existT_l(const t_A u1, const t_P u2, const T1 f) const {
        return sigT<t_A, t_P>::existt(u1, u2).eq_sigT_rect(*(this), f);
      }

      template <typename T1> T1 eq_sigT_rec() const {
        return this->eq_sigT_rect();
      }

      template <typename T1>
      T1 eq_sigT_rect(const sigT<t_A, t_P> &, const T1 f) const {
        return f;
      }

      Prod<t_A, t_P> prod_of_sigT() const {
        return Prod<t_A, t_P>::pair((*(this)).projT1(), (*(this)).projT2());
      }

      t_P projT2() const {
        auto &&_sv = *(this);
        const auto &[d_x, d_a1] =
            std::get<typename sigT<t_A, t_P>::ExistT>(_sv.v());
        return d_a1;
      }

      t_A projT1() const {
        auto &&_sv = *(this);
        const auto &[d_x, d_a1] =
            std::get<typename sigT<t_A, t_P>::ExistT>(_sv.v());
        return d_x;
      }

      template <typename T1, MapsTo<T1, t_A, t_P> F0>
      T1 sigT_rec(F0 &&f) const {
        auto &&_sv = *(this);
        const auto &[d_x, d_a1] =
            std::get<typename sigT<t_A, t_P>::ExistT>(_sv.v());
        return f(d_x, d_a1);
      }

      template <typename T1, MapsTo<T1, t_A, t_P> F0>
      T1 sigT_rect(F0 &&f) const {
        auto &&_sv = *(this);
        const auto &[d_x, d_a1] =
            std::get<typename sigT<t_A, t_P>::ExistT>(_sv.v());
        return f(d_x, d_a1);
      }
    };

    template <typename t_A, typename t_P, typename t_Q> struct sigT2 {
      // TYPES
      struct ExistT2 {
        t_A d_x;
        t_P d_a1;
        t_Q d_a2;
      };

      using variant_t = std::variant<ExistT2>;

    private:
      // DATA
      variant_t d_v_;

    public:
      // CREATORS
      sigT2() {}

      explicit sigT2(ExistT2 _v) : d_v_(std::move(_v)) {}

      sigT2(const sigT2<t_A, t_P, t_Q> &_other)
          : d_v_(std::move(_other.clone().d_v_)) {}

      sigT2(sigT2<t_A, t_P, t_Q> &&_other) : d_v_(std::move(_other.d_v_)) {}

      sigT2<t_A, t_P, t_Q> &operator=(const sigT2<t_A, t_P, t_Q> &_other) {
        d_v_ = std::move(_other.clone().d_v_);
        return *this;
      }

      sigT2<t_A, t_P, t_Q> &operator=(sigT2<t_A, t_P, t_Q> &&_other) {
        d_v_ = std::move(_other.d_v_);
        return *this;
      }

      // ACCESSORS
      sigT2<t_A, t_P, t_Q> clone() const {
        auto &&_sv = *(this);
        const auto &[d_x, d_a1, d_a2] = std::get<ExistT2>(_sv.v());
        return sigT2<t_A, t_P, t_Q>(ExistT2{d_x, d_a1, d_a2});
      }

      // CREATORS
      template <typename _U0, typename _U1, typename _U2>
      explicit sigT2(const sigT2<_U0, _U1, _U2> &_other) {
        const auto &[d_x, d_a1, d_a2] =
            std::get<typename sigT2<_U0, _U1, _U2>::ExistT2>(_other.v());
        d_v_ = ExistT2{t_A(d_x), t_P(d_a1), t_Q(d_a2)};
      }

      static sigT2<t_A, t_P, t_Q> existt2(t_A x, t_P a1, t_Q a2) {
        return sigT2(ExistT2{std::move(x), std::move(a1), std::move(a2)});
      }

      // MANIPULATORS
      inline variant_t &v_mut() { return d_v_; }

      // ACCESSORS
      const variant_t &v() const { return d_v_; }

      template <typename T1> T1 eq_sigT2_rec_uncurried() const {
        return this->eq_sigT2_rect_uncurried();
      }

      template <typename T1>
      T1 eq_sigT2_rect_uncurried(const sigT2<t_A, t_P, t_Q> &v,
                                 const T1 f) const {
        return (*(this)).eq_sigT2_rect(v, [=]() mutable { return f; }());
      }

      template <typename T1>
      T1 eq_sigT2_rect_existT2_r(const t_A v1, const t_P v2, const t_Q v3,
                                 const T1 f) const {
        return (*(this)).eq_sigT2_rect(
            sigT2<t_A, t_P, t_Q>::existt2(v1, v2, v3), f);
      }

      template <typename T1>
      T1 eq_sigT2_rect_existT2_l(const t_A u1, const t_P u2, const t_Q u3,
                                 const T1 f) const {
        return sigT2<t_A, t_P, t_Q>::existt2(u1, u2, u3)
            .eq_sigT2_rect(*(this), f);
      }

      template <typename T1> T1 eq_sigT2_rec() const {
        return this->eq_sigT2_rect();
      }

      template <typename T1>
      T1 eq_sigT2_rect(const sigT2<t_A, t_P, t_Q> &, const T1 f) const {
        return f;
      }

      t_Q projT3() const {
        auto &&_sv = *(this);
        const auto &[d_x, d_a1, d_a2] =
            std::get<typename sigT2<t_A, t_P, t_Q>::ExistT2>(_sv.v());
        return d_a2;
      }

      sigT<t_A, t_P> sigT_of_sigT2() const {
        sigT2<t_A, t_P, t_Q> _self = *(this);
        return sigT<t_A, t_P>::existt(
            [=]() mutable {
              const auto &[d_x, d_a1, d_a2] =
                  std::get<typename sigT2<t_A, t_P, t_Q>::ExistT2>(_self.v());
              return d_x;
            }(),
            [=]() mutable {
              const auto &[d_x0, d_a10, d_a20] =
                  std::get<typename sigT2<t_A, t_P, t_Q>::ExistT2>(_self.v());
              return d_a10;
            }());
      }

      template <typename T1, MapsTo<T1, t_A, t_P, t_Q> F0>
      T1 sigT2_rec(F0 &&f) const {
        auto &&_sv = *(this);
        const auto &[d_x, d_a1, d_a2] =
            std::get<typename sigT2<t_A, t_P, t_Q>::ExistT2>(_sv.v());
        return f(d_x, d_a1, d_a2);
      }

      template <typename T1, MapsTo<T1, t_A, t_P, t_Q> F0>
      T1 sigT2_rect(F0 &&f) const {
        auto &&_sv = *(this);
        const auto &[d_x, d_a1, d_a2] =
            std::get<typename sigT2<t_A, t_P, t_Q>::ExistT2>(_sv.v());
        return f(d_x, d_a1, d_a2);
      }
    };

    template <typename T1>
    static sig<T1> sig_of_sigT(const sigT<T1, std::any> &x) {
      return sig<T1>::exist(x.projT1());
    }

    template <typename T1>
    static sigT<T1, std::any> sigT_of_sig(const sig<T1> &x) {
      return sigT<T1, std::any>::existt(x.proj1_sig(), std::any{});
    }

    template <typename T1>
    static sig2<T1> sig2_of_sigT2(const sigT2<T1, std::any, std::any> &x) {
      return sig2<T1>::exist2(x.sigT_of_sigT2().projT1());
    }

    template <typename T1>
    static sigT2<T1, std::any, std::any> sigT2_of_sig2(const sig2<T1> &x) {
      return sigT2<T1, std::any, std::any>::existt2(x.sig_of_sig2().proj1_sig(),
                                                    std::any{}, std::any{});
    }

    template <typename T1, typename T2>
    static sigT<T1, T2> sigT_of_prod(const Prod<T1, T2> &p) {
      return sigT<T1, T2>::existt(p.fst(), p.snd());
    }

    template <typename T1, typename T2, typename T3>
    static T3 eq_sigT_rect_existT(const T1 u1, const T2 u2, const T1 v1,
                                  const T2 v2, const T3 f) {
      return sigT<T1, T2>::existt(u1, u2).eq_sigT_rect(
          sigT<T1, T2>::existt(v1, v2), f);
    }

    template <typename T1, typename T2>
    static T2 eq_sig_rect_exist(const T1 u1, const T1 v1, const T2 f) {
      return sig<T1>::exist(u1).eq_sig_rect(sig<T1>::exist(v1), f);
    }

    template <typename T1, typename T2, typename T3, typename T4>
    static T4 eq_sigT2_rect_existT2(const T1 u1, const T2 u2, const T3 u3,
                                    const T1 v1, const T2 v2, const T3 v3,
                                    const T4 f) {
      return sigT2<T1, T2, T3>::existt2(u1, u2, u3)
          .eq_sigT2_rect(sigT2<T1, T2, T3>::existt2(v1, v2, v3), f);
    }

    template <typename T1, typename T2>
    static T2 eq_sig2_rect_exist2(const T1 u1, const T1 v1, const T2 f) {
      return sig2<T1>::exist2(u1).eq_sig2_rect(sig2<T1>::exist2(v1), f);
    }
    enum class Sumbool { e_LEFT, e_RIGHT };

    template <typename T1>
    static T1 sumbool_rect(const T1 f, const T1 f0, const Sumbool s) {
      switch (s) {
      case Sumbool::e_LEFT: {
        return f;
      }
      case Sumbool::e_RIGHT: {
        return f0;
      }
      default:
        std::unreachable();
      }
    }

    template <typename T1>
    static T1 sumbool_rec(const T1 f, const T1 f0, const Sumbool s) {
      switch (s) {
      case Sumbool::e_LEFT: {
        return f;
      }
      case Sumbool::e_RIGHT: {
        return f0;
      }
      default:
        std::unreachable();
      }
    }

    template <typename t_A> struct sumor {
      // TYPES
      struct Inleft {
        t_A d_a0;
      };

      struct Inright {};

      using variant_t = std::variant<Inleft, Inright>;

    private:
      // DATA
      variant_t d_v_;

    public:
      // CREATORS
      sumor() {}

      explicit sumor(Inleft _v) : d_v_(std::move(_v)) {}

      explicit sumor(Inright _v) : d_v_(_v) {}

      sumor(const sumor<t_A> &_other) : d_v_(std::move(_other.clone().d_v_)) {}

      sumor(sumor<t_A> &&_other) : d_v_(std::move(_other.d_v_)) {}

      sumor<t_A> &operator=(const sumor<t_A> &_other) {
        d_v_ = std::move(_other.clone().d_v_);
        return *this;
      }

      sumor<t_A> &operator=(sumor<t_A> &&_other) {
        d_v_ = std::move(_other.d_v_);
        return *this;
      }

      // ACCESSORS
      sumor<t_A> clone() const {
        auto &&_sv = *(this);
        if (std::holds_alternative<Inleft>(_sv.v())) {
          const auto &[d_a0] = std::get<Inleft>(_sv.v());
          return sumor<t_A>(Inleft{d_a0});
        } else {
          return sumor<t_A>(Inright{});
        }
      }

      // CREATORS
      template <typename _U> explicit sumor(const sumor<_U> &_other) {
        if (std::holds_alternative<typename sumor<_U>::Inleft>(_other.v())) {
          const auto &[d_a0] = std::get<typename sumor<_U>::Inleft>(_other.v());
          d_v_ = Inleft{t_A(d_a0)};
        } else {
          d_v_ = Inright{};
        }
      }

      static sumor<t_A> inleft(t_A a0) { return sumor(Inleft{std::move(a0)}); }

      static sumor<t_A> inright() { return sumor(Inright{}); }

      // MANIPULATORS
      inline variant_t &v_mut() { return d_v_; }

      // ACCESSORS
      const variant_t &v() const { return d_v_; }

      template <typename T1, MapsTo<T1, t_A> F0>
      T1 sumor_rec(F0 &&f, const T1 f0) const {
        auto &&_sv = *(this);
        if (std::holds_alternative<typename sumor<t_A>::Inleft>(_sv.v())) {
          const auto &[d_a0] = std::get<typename sumor<t_A>::Inleft>(_sv.v());
          return f(d_a0);
        } else {
          return f0;
        }
      }

      template <typename T1, MapsTo<T1, t_A> F0>
      T1 sumor_rect(F0 &&f, const T1 f0) const {
        auto &&_sv = *(this);
        if (std::holds_alternative<typename sumor<t_A>::Inleft>(_sv.v())) {
          const auto &[d_a0] = std::get<typename sumor<t_A>::Inleft>(_sv.v());
          return f(d_a0);
        } else {
          return f0;
        }
      }
    };

    template <typename T1, typename T2, MapsTo<sig<T2>, T1> F0>
    static sig<std::function<T2(T1)>> Choice(F0 &&h) {
      return sig<std::function<T2(T1)>>::exist(
          [=](const T1 z) mutable { return h(z).proj1_sig(); });
    }

    template <typename T1, typename T2, typename T3,
              MapsTo<sigT<T2, T3>, T1> F0>
    static sigT<std::function<T2(T1)>, std::function<T3(T1)>> Choice2(F0 &&h) {
      return sigT<std::function<T2(T1)>, std::function<T3(T1)>>::existt(
          [=](const T1 z) mutable { return h(z).projT1(); },
          [=](const T1 z) mutable {
            sigT<T2, T3> s = h(z);
            auto &[d_x, d_a1] =
                std::get<typename sigT<T2, T3>::ExistT>(s.v_mut());
            return d_a1;
          });
    }

    template <typename T1, MapsTo<Sumbool, T1> F0>
    static sig<std::function<Bool0(T1)>> bool_choice(F0 &&h) {
      return sig<std::function<Bool0(T1)>>::exist([=](const T1 z) mutable {
        switch (h(z)) {
        case Sumbool::e_LEFT: {
          return Bool0::e_TRUE0;
        }
        case Sumbool::e_RIGHT: {
          return Bool0::e_FALSE0;
        }
        default:
          std::unreachable();
        }
      });
    }

    template <typename T1, MapsTo<sig<T1>, T1> F0>
    static sig<std::function<T1(Nat)>> dependent_choice(F0 &&h, const T1 x0) {
      auto f_impl = [=](auto &_self_f, Nat n) mutable -> T1 {
        if (std::holds_alternative<typename Nat::O>(n.v())) {
          return x0;
        } else {
          const auto &[d_a0] = std::get<typename Nat::S>(n.v());
          return h(_self_f(_self_f, *(d_a0))).proj1_sig();
        }
      };
      auto f = [=](Nat n) mutable -> T1 { return f_impl(f_impl, n); };
      return sig<std::function<T1(Nat)>>::exist(f);
    }

    template <typename a> using Exc = Option<a>;

    template <typename T1> static Option<T1> value(const T1 x) {
      return Option<T1>::some(x);
    }

    template <typename T1> static const Option<T1> &error() {
      static const Option<T1> v = Option<T1>::none();
      return v;
    }

    template <typename T1> static const T1 &except() {
      static const T1 v = []() { throw std::logic_error("absurd case"); }();
      return v;
    }

    template <typename T1> static const T1 &absurd_set() {
      static const T1 v = []() { throw std::logic_error("absurd case"); }();
      return v;
    }
  };
};

#endif // INCLUDED_ROCQ_BUG_14174
