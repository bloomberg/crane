#ifndef INCLUDED_LEVENSHTEIN
#define INCLUDED_LEVENSHTEIN

#include <functional>
#include <memory>
#include <optional>
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
  __attribute__((pure)) Nat clone() const {
    auto &&_sv = *(this);
    if (std::holds_alternative<O>(_sv.v())) {
      return Nat(O{});
    } else {
      const auto &[d_a0] = std::get<S>(_sv.v());
      return Nat(S{d_a0 ? std::make_unique<Nat>(d_a0->clone()) : nullptr});
    }
  }

  // CREATORS
  __attribute__((pure)) static Nat o() { return Nat(O{}); }

  __attribute__((pure)) static Nat s(Nat a0) {
    return Nat(S{std::make_unique<Nat>(std::move(a0))});
  }

  // MANIPULATORS
  ~Nat() {
    std::vector<std::unique_ptr<Nat>> _stack;
    auto _drain = [&](Nat &_node) {
      if (std::holds_alternative<S>(_node.d_v_)) {
        auto &_alt = std::get<S>(_node.d_v_);
        if (_alt.d_a0)
          _stack.push_back(std::move(_alt.d_a0));
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
  __attribute__((pure)) const variant_t &v() const { return d_v_; }

  __attribute__((pure)) Bool0 leb(const Nat &m) const {
    auto &&_sv = *(this);
    if (std::holds_alternative<typename Nat::O>(_sv.v())) {
      return Bool0::e_TRUE0;
    } else {
      const auto &[d_a0] = std::get<typename Nat::S>(_sv.v());
      if (std::holds_alternative<typename Nat::O>(m.v())) {
        return Bool0::e_FALSE0;
      } else {
        const auto &[d_a00] = std::get<typename Nat::S>(m.v());
        return (*(d_a0)).leb(*(d_a00));
      }
    }
  }
};

template <typename t_A, typename t_P> struct SigT {
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
  SigT() {}

  explicit SigT(ExistT _v) : d_v_(std::move(_v)) {}

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
  __attribute__((pure)) SigT<t_A, t_P> clone() const {
    auto &&_sv = *(this);
    const auto &[d_x, d_a1] = std::get<ExistT>(_sv.v());
    return SigT<t_A, t_P>(ExistT{d_x, d_a1});
  }

  // CREATORS
  template <typename _U0, typename _U1>
  explicit SigT(const SigT<_U0, _U1> &_other) {
    const auto &[d_x, d_a1] =
        std::get<typename SigT<_U0, _U1>::ExistT>(_other.v());
    d_v_ = ExistT{t_A(d_x), t_P(d_a1)};
  }

  __attribute__((pure)) static SigT<t_A, t_P> existt(t_A x, t_P a1) {
    return SigT(ExistT{std::move(x), std::move(a1)});
  }

  // MANIPULATORS
  inline variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }

  t_A projT1() const {
    auto &&_sv = *(this);
    const auto &[d_x, d_a1] =
        std::get<typename SigT<t_A, t_P>::ExistT>(_sv.v());
    return d_x;
  }
};
enum class Sumbool { e_LEFT, e_RIGHT };

struct Bool {
  __attribute__((pure)) static Sumbool bool_dec(const Bool0 b1, const Bool0 b2);
};

struct Ascii {
  // TYPES
  struct Ascii0 {
    Bool0 d_a0;
    Bool0 d_a1;
    Bool0 d_a2;
    Bool0 d_a3;
    Bool0 d_a4;
    Bool0 d_a5;
    Bool0 d_a6;
    Bool0 d_a7;
  };

  using variant_t = std::variant<Ascii0>;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  Ascii() {}

  explicit Ascii(Ascii0 _v) : d_v_(std::move(_v)) {}

  Ascii(const Ascii &_other) : d_v_(std::move(_other.clone().d_v_)) {}

  Ascii(Ascii &&_other) : d_v_(std::move(_other.d_v_)) {}

  Ascii &operator=(const Ascii &_other) {
    d_v_ = std::move(_other.clone().d_v_);
    return *this;
  }

  Ascii &operator=(Ascii &&_other) {
    d_v_ = std::move(_other.d_v_);
    return *this;
  }

  // ACCESSORS
  __attribute__((pure)) Ascii clone() const {
    auto &&_sv = *(this);
    const auto &[d_a0, d_a1, d_a2, d_a3, d_a4, d_a5, d_a6, d_a7] =
        std::get<Ascii0>(_sv.v());
    return Ascii(Ascii0{d_a0, d_a1, d_a2, d_a3, d_a4, d_a5, d_a6, d_a7});
  }

  // CREATORS
  __attribute__((pure)) static Ascii ascii0(Bool0 a0, Bool0 a1, Bool0 a2,
                                            Bool0 a3, Bool0 a4, Bool0 a5,
                                            Bool0 a6, Bool0 a7) {
    return Ascii(Ascii0{std::move(a0), std::move(a1), std::move(a2),
                        std::move(a3), std::move(a4), std::move(a5),
                        std::move(a6), std::move(a7)});
  }

  // MANIPULATORS
  inline variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }

  __attribute__((pure)) Sumbool ascii_dec(const Ascii &b) const {
    auto &&_sv = *(this);
    const auto &[d_a0, d_a1, d_a2, d_a3, d_a4, d_a5, d_a6, d_a7] =
        std::get<typename Ascii::Ascii0>(_sv.v());
    const auto &[d_a00, d_a10, d_a20, d_a30, d_a40, d_a50, d_a60, d_a70] =
        std::get<typename Ascii::Ascii0>(b.v());
    switch (Bool::bool_dec(d_a0, d_a00)) {
    case Sumbool::e_LEFT: {
      switch (Bool::bool_dec(d_a1, d_a10)) {
      case Sumbool::e_LEFT: {
        switch (Bool::bool_dec(d_a2, d_a20)) {
        case Sumbool::e_LEFT: {
          switch (Bool::bool_dec(d_a3, d_a30)) {
          case Sumbool::e_LEFT: {
            switch (Bool::bool_dec(d_a4, d_a40)) {
            case Sumbool::e_LEFT: {
              switch (Bool::bool_dec(d_a5, d_a50)) {
              case Sumbool::e_LEFT: {
                switch (Bool::bool_dec(d_a6, d_a60)) {
                case Sumbool::e_LEFT: {
                  switch (Bool::bool_dec(d_a7, d_a70)) {
                  case Sumbool::e_LEFT: {
                    return Sumbool::e_LEFT;
                  }
                  case Sumbool::e_RIGHT: {
                    return Sumbool::e_RIGHT;
                  }
                  default:
                    std::unreachable();
                  }
                }
                case Sumbool::e_RIGHT: {
                  return Sumbool::e_RIGHT;
                }
                default:
                  std::unreachable();
                }
              }
              case Sumbool::e_RIGHT: {
                return Sumbool::e_RIGHT;
              }
              default:
                std::unreachable();
              }
            }
            case Sumbool::e_RIGHT: {
              return Sumbool::e_RIGHT;
            }
            default:
              std::unreachable();
            }
          }
          case Sumbool::e_RIGHT: {
            return Sumbool::e_RIGHT;
          }
          default:
            std::unreachable();
          }
        }
        case Sumbool::e_RIGHT: {
          return Sumbool::e_RIGHT;
        }
        default:
          std::unreachable();
        }
      }
      case Sumbool::e_RIGHT: {
        return Sumbool::e_RIGHT;
      }
      default:
        std::unreachable();
      }
    }
    case Sumbool::e_RIGHT: {
      return Sumbool::e_RIGHT;
    }
    default:
      std::unreachable();
    }
  }
};

struct String {
  // TYPES
  struct EmptyString {};

  struct String0 {
    Ascii d_a0;
    std::unique_ptr<String> d_a1;
  };

  using variant_t = std::variant<EmptyString, String0>;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  String() {}

  explicit String(EmptyString _v) : d_v_(_v) {}

  explicit String(String0 _v) : d_v_(std::move(_v)) {}

  String(const String &_other) : d_v_(std::move(_other.clone().d_v_)) {}

  String(String &&_other) : d_v_(std::move(_other.d_v_)) {}

  String &operator=(const String &_other) {
    d_v_ = std::move(_other.clone().d_v_);
    return *this;
  }

  String &operator=(String &&_other) {
    d_v_ = std::move(_other.d_v_);
    return *this;
  }

  // ACCESSORS
  __attribute__((pure)) String clone() const {
    auto &&_sv = *(this);
    if (std::holds_alternative<EmptyString>(_sv.v())) {
      return String(EmptyString{});
    } else {
      const auto &[d_a0, d_a1] = std::get<String0>(_sv.v());
      return String(
          String0{d_a0.clone(),
                  d_a1 ? std::make_unique<String>(d_a1->clone()) : nullptr});
    }
  }

  // CREATORS
  __attribute__((pure)) static String emptystring() {
    return String(EmptyString{});
  }

  __attribute__((pure)) static String string0(Ascii a0, String a1) {
    return String(
        String0{std::move(a0), std::make_unique<String>(std::move(a1))});
  }

  // MANIPULATORS
  ~String() {
    std::vector<std::unique_ptr<String>> _stack;
    auto _drain = [&](String &_node) {
      if (std::holds_alternative<String0>(_node.d_v_)) {
        auto &_alt = std::get<String0>(_node.d_v_);
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
  __attribute__((pure)) const variant_t &v() const { return d_v_; }

  __attribute__((pure)) String append(String s2) const {
    auto &&_sv = *(this);
    if (std::holds_alternative<typename String::EmptyString>(_sv.v())) {
      return s2;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename String::String0>(_sv.v());
      return String::string0(d_a0, (*(d_a1)).append(std::move(s2)));
    }
  }

  __attribute__((pure)) Nat length() const {
    auto &&_sv = *(this);
    if (std::holds_alternative<typename String::EmptyString>(_sv.v())) {
      return Nat::o();
    } else {
      const auto &[d_a0, d_a1] = std::get<typename String::String0>(_sv.v());
      return Nat::s((*(d_a1)).length());
    }
  }
};

struct Levenshtein {
  struct edit {
    // TYPES
    struct Insertion {
      Ascii d_a;
      String d_s;
    };

    struct Deletion {
      Ascii d_a;
      String d_s;
    };

    struct Update {
      Ascii d_a;
      Ascii d_a_1;
      String d_neq;
    };

    using variant_t = std::variant<Insertion, Deletion, Update>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    edit() {}

    explicit edit(Insertion _v) : d_v_(std::move(_v)) {}

    explicit edit(Deletion _v) : d_v_(std::move(_v)) {}

    explicit edit(Update _v) : d_v_(std::move(_v)) {}

    edit(const edit &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    edit(edit &&_other) : d_v_(std::move(_other.d_v_)) {}

    edit &operator=(const edit &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    edit &operator=(edit &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) edit clone() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<Insertion>(_sv.v())) {
        const auto &[d_a, d_s] = std::get<Insertion>(_sv.v());
        return edit(Insertion{d_a.clone(), d_s.clone()});
      } else if (std::holds_alternative<Deletion>(_sv.v())) {
        const auto &[d_a, d_s] = std::get<Deletion>(_sv.v());
        return edit(Deletion{d_a.clone(), d_s.clone()});
      } else {
        const auto &[d_a, d_a_1, d_neq] = std::get<Update>(_sv.v());
        return edit(Update{d_a.clone(), d_a_1.clone(), d_neq.clone()});
      }
    }

    // CREATORS
    __attribute__((pure)) static edit insertion(Ascii a, String s) {
      return edit(Insertion{std::move(a), std::move(s)});
    }

    __attribute__((pure)) static edit deletion(Ascii a, String s) {
      return edit(Deletion{std::move(a), std::move(s)});
    }

    __attribute__((pure)) static edit update(Ascii a, Ascii a_1, String neq) {
      return edit(Update{std::move(a), std::move(a_1), std::move(neq)});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    template <typename T1, MapsTo<T1, Ascii, String> F0,
              MapsTo<T1, Ascii, String> F1, MapsTo<T1, Ascii, Ascii, String> F2>
    T1 edit_rec(F0 &&f, F1 &&f0, F2 &&f1, const String &,
                const String &) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename edit::Insertion>(_sv.v())) {
        const auto &[d_a, d_s] = std::get<typename edit::Insertion>(_sv.v());
        return f(d_a, d_s);
      } else if (std::holds_alternative<typename edit::Deletion>(_sv.v())) {
        const auto &[d_a, d_s] = std::get<typename edit::Deletion>(_sv.v());
        return f0(d_a, d_s);
      } else {
        const auto &[d_a, d_a_1, d_neq] =
            std::get<typename edit::Update>(_sv.v());
        return f1(d_a, d_a_1, d_neq);
      }
    }

    template <typename T1, MapsTo<T1, Ascii, String> F0,
              MapsTo<T1, Ascii, String> F1, MapsTo<T1, Ascii, Ascii, String> F2>
    T1 edit_rect(F0 &&f, F1 &&f0, F2 &&f1, const String &,
                 const String &) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename edit::Insertion>(_sv.v())) {
        const auto &[d_a, d_s] = std::get<typename edit::Insertion>(_sv.v());
        return f(d_a, d_s);
      } else if (std::holds_alternative<typename edit::Deletion>(_sv.v())) {
        const auto &[d_a, d_s] = std::get<typename edit::Deletion>(_sv.v());
        return f0(d_a, d_s);
      } else {
        const auto &[d_a, d_a_1, d_neq] =
            std::get<typename edit::Update>(_sv.v());
        return f1(d_a, d_a_1, d_neq);
      }
    }
  };

  struct chain {
    // TYPES
    struct Empty {};

    struct Skip {
      Ascii d_a;
      String d_s;
      String d_t;
      Nat d_n;
      std::unique_ptr<chain> d_a4;
    };

    struct Change {
      String d_s;
      String d_t;
      String d_u;
      Nat d_n;
      edit d_a4;
      std::unique_ptr<chain> d_a5;
    };

    using variant_t = std::variant<Empty, Skip, Change>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    chain() {}

    explicit chain(Empty _v) : d_v_(_v) {}

    explicit chain(Skip _v) : d_v_(std::move(_v)) {}

    explicit chain(Change _v) : d_v_(std::move(_v)) {}

    chain(const chain &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    chain(chain &&_other) : d_v_(std::move(_other.d_v_)) {}

    chain &operator=(const chain &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    chain &operator=(chain &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) chain clone() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<Empty>(_sv.v())) {
        return chain(Empty{});
      } else if (std::holds_alternative<Skip>(_sv.v())) {
        const auto &[d_a, d_s, d_t, d_n, d_a4] = std::get<Skip>(_sv.v());
        return chain(
            Skip{d_a.clone(), d_s.clone(), d_t.clone(), d_n.clone(),
                 d_a4 ? std::make_unique<Levenshtein::chain>(d_a4->clone())
                      : nullptr});
      } else {
        const auto &[d_s, d_t, d_u, d_n, d_a4, d_a5] =
            std::get<Change>(_sv.v());
        return chain(Change{
            d_s.clone(), d_t.clone(), d_u.clone(), d_n.clone(), d_a4.clone(),
            d_a5 ? std::make_unique<Levenshtein::chain>(d_a5->clone())
                 : nullptr});
      }
    }

    // CREATORS
    __attribute__((pure)) static chain empty() { return chain(Empty{}); }

    __attribute__((pure)) static chain skip(Ascii a, String s, String t, Nat n,
                                            chain a4) {
      return chain(Skip{std::move(a), std::move(s), std::move(t), std::move(n),
                        std::make_unique<chain>(std::move(a4))});
    }

    __attribute__((pure)) static chain change(String s, String t, String u,
                                              Nat n, edit a4, chain a5) {
      return chain(Change{std::move(s), std::move(t), std::move(u),
                          std::move(n), std::move(a4),
                          std::make_unique<chain>(std::move(a5))});
    }

    // MANIPULATORS
    ~chain() {
      std::vector<std::unique_ptr<chain>> _stack;
      auto _drain = [&](chain &_node) {
        if (std::holds_alternative<Skip>(_node.d_v_)) {
          auto &_alt = std::get<Skip>(_node.d_v_);
          if (_alt.d_a4)
            _stack.push_back(std::move(_alt.d_a4));
        }
        if (std::holds_alternative<Change>(_node.d_v_)) {
          auto &_alt = std::get<Change>(_node.d_v_);
          if (_alt.d_a5)
            _stack.push_back(std::move(_alt.d_a5));
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
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    __attribute__((pure)) chain aux_eq_char(const String &, const String &,
                                            const Ascii &, String xs, Ascii y,
                                            String ys, Nat n) const {
      return chain::skip(std::move(y), std::move(xs), std::move(ys),
                         std::move(n), std::move(*(this)));
    }

    __attribute__((pure)) chain aux_update(const String &, const String &,
                                           const Ascii &x, const String &xs,
                                           const Ascii &y, const String &ys,
                                           const Nat &n) const {
      return (*(this)).update_chain(x, y, xs, ys, n);
    }

    __attribute__((pure)) chain aux_delete(const String &, const String &,
                                           const Ascii &x, const String &xs,
                                           Ascii y, String ys,
                                           const Nat &n) const {
      return (*(this)).delete_chain(
          x, xs, String::string0(std::move(y), std::move(ys)), n);
    }

    __attribute__((pure)) chain aux_insert(const String &, const String &,
                                           Ascii x, String xs, const Ascii &y,
                                           const String &ys,
                                           const Nat &n) const {
      return (*(this)).insert_chain(
          y, String::string0(std::move(x), std::move(xs)), ys, n);
    }

    __attribute__((pure)) chain update_chain(Ascii c, Ascii c_, String s1,
                                             String s2, Nat n) const {
      return chain::change(String::string0(c, s1), String::string0(c_, s1),
                           String::string0(c_, s2), n, edit::update(c, c_, s1),
                           chain::skip(c_, s1, s2, n, std::move(*(this))));
    }

    __attribute__((pure)) chain delete_chain(Ascii c, String s1, String s2,
                                             Nat n) const {
      return chain::change(String::string0(c, s1), s1, std::move(s2),
                           std::move(n), edit::deletion(c, s1),
                           std::move(*(this)));
    }

    __attribute__((pure)) chain insert_chain(Ascii c, String s1, String s2,
                                             Nat n) const {
      return chain::change(s1, String::string0(c, s1), String::string0(c, s2),
                           n, edit::insertion(c, s1),
                           chain::skip(c, s1, s2, n, std::move(*(this))));
    }

    template <typename T1, MapsTo<T1, Ascii, String, String, Nat, chain, T1> F1,
              MapsTo<T1, String, String, String, Nat, edit, chain, T1> F2>
    T1 chain_rec(const T1 f, F1 &&f0, F2 &&f1, const String &, const String &,
                 const Nat &) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename chain::Empty>(_sv.v())) {
        return f;
      } else if (std::holds_alternative<typename chain::Skip>(_sv.v())) {
        const auto &[d_a, d_s, d_t, d_n, d_a4] =
            std::get<typename chain::Skip>(_sv.v());
        return f0(d_a, d_s, d_t, d_n, *(d_a4),
                  (*(d_a4)).template chain_rec<T1>(f, f0, f1, d_s, d_t, d_n));
      } else {
        const auto &[d_s, d_t, d_u, d_n, d_a4, d_a5] =
            std::get<typename chain::Change>(_sv.v());
        return f1(d_s, d_t, d_u, d_n, d_a4, *(d_a5),
                  (*(d_a5)).template chain_rec<T1>(f, f0, f1, d_t, d_u, d_n));
      }
    }

    template <typename T1, MapsTo<T1, Ascii, String, String, Nat, chain, T1> F1,
              MapsTo<T1, String, String, String, Nat, edit, chain, T1> F2>
    T1 chain_rect(const T1 f, F1 &&f0, F2 &&f1, const String &, const String &,
                  const Nat &) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename chain::Empty>(_sv.v())) {
        return f;
      } else if (std::holds_alternative<typename chain::Skip>(_sv.v())) {
        const auto &[d_a, d_s, d_t, d_n, d_a4] =
            std::get<typename chain::Skip>(_sv.v());
        return f0(d_a, d_s, d_t, d_n, *(d_a4),
                  (*(d_a4)).template chain_rect<T1>(f, f0, f1, d_s, d_t, d_n));
      } else {
        const auto &[d_s, d_t, d_u, d_n, d_a4, d_a5] =
            std::get<typename chain::Change>(_sv.v());
        return f1(d_s, d_t, d_u, d_n, d_a4, *(d_a5),
                  (*(d_a5)).template chain_rect<T1>(f, f0, f1, d_t, d_u, d_n));
      }
    }
  };

  __attribute__((pure)) static chain same_chain(const String &s);

  template <typename T1> static T1 _inserts_chain_F(const String s) {
    if (std::holds_alternative<typename String::EmptyString>(s.v())) {
      return chain::empty();
    } else {
      const auto &[d_a00, d_a10] = std::get<typename String::String0>(s.v());
      return chain::skip(d_a00, *(d_a10), *(d_a10), Nat::o(),
                         _inserts_chain_F<T1>(*(d_a10)));
    }
  }

  __attribute__((pure)) static chain inserts_chain(const String &s1,
                                                   const String &s2);
  __attribute__((pure)) static chain inserts_chain_empty(const String &s);
  __attribute__((pure)) static chain deletes_chain(const String &s1,
                                                   const String &s2);
  __attribute__((pure)) static chain deletes_chain_empty(const String &s);
  __attribute__((pure)) static chain aux_both_empty(const String &_x,
                                                    const String &_x0);

  template <typename T1, MapsTo<Nat, T1> F3>
  static T1 min3_app(const T1 x, const T1 y, const T1 z, F3 &&f) {
    Nat n1 = f(x);
    Nat n2 = f(y);
    Nat n3 = f(z);
    switch (n1.leb(n2)) {
    case Bool0::e_TRUE0: {
      switch (std::move(n1).leb(std::move(n3))) {
      case Bool0::e_TRUE0: {
        return x;
      }
      case Bool0::e_FALSE0: {
        return z;
      }
      default:
        std::unreachable();
      }
    }
    case Bool0::e_FALSE0: {
      switch (std::move(n2).leb(std::move(n3))) {
      case Bool0::e_TRUE0: {
        return y;
      }
      case Bool0::e_FALSE0: {
        return z;
      }
      default:
        std::unreachable();
      }
    }
    default:
      std::unreachable();
    }
  }

  __attribute__((pure)) static SigT<Nat, chain>
  levenshtein_chain(const String &s, String _x0);
  __attribute__((pure)) static Nat levenshtein_computed(const String &s,
                                                        const String &t);
  __attribute__((pure)) static Nat levenshtein(const String &_x0,
                                               const String &_x1);
};

#endif // INCLUDED_LEVENSHTEIN
