#ifndef INCLUDED_LEVENSHTEIN
#define INCLUDED_LEVENSHTEIN

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

enum class Bool0 { TRUE_, FALSE_ };

struct Nat {
  // TYPES
  struct O {};

  struct S {
    std::shared_ptr<Nat> a0;
  };

  using variant_t = std::variant<O, S>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  Nat() {}

  explicit Nat(O _v) : v_(_v) {}

  explicit Nat(S _v) : v_(std::move(_v)) {}

  Nat(const Nat &_other) : v_(std::move(_other.clone().v_)) {}

  Nat(Nat &&_other) noexcept : v_(std::move(_other.v_)) {}

  Nat &operator=(const Nat &_other) {
    v_ = std::move(_other.clone().v_);
    return *this;
  }

  Nat &operator=(Nat &&_other) noexcept {
    v_ = std::move(_other.v_);
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
    _stack.reserve(8);
    _stack.push_back({this, &_out});
    while (!_stack.empty()) {
      auto _frame = _stack.back();
      _stack.pop_back();
      const Nat *_src = _frame._src;
      Nat *_dst = _frame._dst;
      if (std::holds_alternative<O>(_src->v())) {
        _dst->v_ = O{};
      } else {
        const auto &_alt = std::get<S>(_src->v());
        _dst->v_ = S{_alt.a0 ? std::make_shared<Nat>() : nullptr};
        auto &_dst_alt = std::get<S>(_dst->v_);
        if (_alt.a0) {
          _stack.push_back({_alt.a0.get(), _dst_alt.a0.get()});
        }
      }
    }
    return _out;
  }

  // CREATORS
  static Nat o() { return Nat(O{}); }

  static Nat s(Nat a0) { return Nat(S{std::make_shared<Nat>(std::move(a0))}); }

  // MANIPULATORS
  ~Nat() {
    std::vector<std::shared_ptr<Nat>> _stack{};
    _stack.reserve(8);
    auto _drain = [&](Nat &_node) {
      if (std::holds_alternative<S>(_node.v_)) {
        auto &_alt = std::get<S>(_node.v_);
        if (_alt.a0) {
          _stack.push_back(std::move(_alt.a0));
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

  Bool0 leb(const Nat &m) const {
    if (std::holds_alternative<typename Nat::O>(this->v())) {
      return Bool0::TRUE_;
    } else {
      const auto &[a0] = std::get<typename Nat::S>(this->v());
      if (std::holds_alternative<typename Nat::O>(m.v())) {
        return Bool0::FALSE_;
      } else {
        const auto &[a00] = std::get<typename Nat::S>(m.v());
        return a0->leb(*a00);
      }
    }
  }
};

template <typename A, typename P> struct SigT {
  // DATA
  A x;
  P a1;

  // ACCESSORS
  SigT<A, P> clone() const { return {x, a1}; }

  // CREATORS
  static SigT<A, P> existt(A x, P a1) { return {std::move(x), std::move(a1)}; }

  A projT1() const {
    const auto &[x0, a1] = *this;
    return x0;
  }
};
enum class Sumbool { LEFT, RIGHT };

struct Bool {
  static Sumbool bool_dec(Bool0 b1, Bool0 b2);
};

struct Ascii {
  // DATA
  Bool0 a0;
  Bool0 a1;
  Bool0 a2;
  Bool0 a3;
  Bool0 a4;
  Bool0 a5;
  Bool0 a6;
  Bool0 a7;

  // ACCESSORS
  Ascii clone() const { return {a0, a1, a2, a3, a4, a5, a6, a7}; }

  // CREATORS
  static Ascii ascii0(Bool0 a0, Bool0 a1, Bool0 a2, Bool0 a3, Bool0 a4,
                      Bool0 a5, Bool0 a6, Bool0 a7) {
    return {a0, a1, a2, a3, a4, a5, a6, a7};
  }

  Sumbool ascii_dec(const Ascii &b) const {
    const auto &[a0, a1, a2, a3, a4, a5, a6, a7] = *this;
    const auto &[a00, a10, a20, a30, a40, a50, a60, a70] = b;
    switch (Bool::bool_dec(a0, a00)) {
    case Sumbool::LEFT: {
      switch (Bool::bool_dec(a1, a10)) {
      case Sumbool::LEFT: {
        switch (Bool::bool_dec(a2, a20)) {
        case Sumbool::LEFT: {
          switch (Bool::bool_dec(a3, a30)) {
          case Sumbool::LEFT: {
            switch (Bool::bool_dec(a4, a40)) {
            case Sumbool::LEFT: {
              switch (Bool::bool_dec(a5, a50)) {
              case Sumbool::LEFT: {
                switch (Bool::bool_dec(a6, a60)) {
                case Sumbool::LEFT: {
                  switch (Bool::bool_dec(a7, a70)) {
                  case Sumbool::LEFT: {
                    return Sumbool::LEFT;
                  }
                  case Sumbool::RIGHT: {
                    return Sumbool::RIGHT;
                  }
                  default:
                    std::unreachable();
                  }
                }
                case Sumbool::RIGHT: {
                  return Sumbool::RIGHT;
                }
                default:
                  std::unreachable();
                }
              }
              case Sumbool::RIGHT: {
                return Sumbool::RIGHT;
              }
              default:
                std::unreachable();
              }
            }
            case Sumbool::RIGHT: {
              return Sumbool::RIGHT;
            }
            default:
              std::unreachable();
            }
          }
          case Sumbool::RIGHT: {
            return Sumbool::RIGHT;
          }
          default:
            std::unreachable();
          }
        }
        case Sumbool::RIGHT: {
          return Sumbool::RIGHT;
        }
        default:
          std::unreachable();
        }
      }
      case Sumbool::RIGHT: {
        return Sumbool::RIGHT;
      }
      default:
        std::unreachable();
      }
    }
    case Sumbool::RIGHT: {
      return Sumbool::RIGHT;
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
    Ascii a0;
    std::shared_ptr<String> a1;
  };

  using variant_t = std::variant<EmptyString, String0>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  String() {}

  explicit String(EmptyString _v) : v_(_v) {}

  explicit String(String0 _v) : v_(std::move(_v)) {}

  String(const String &_other) : v_(std::move(_other.clone().v_)) {}

  String(String &&_other) noexcept : v_(std::move(_other.v_)) {}

  String &operator=(const String &_other) {
    v_ = std::move(_other.clone().v_);
    return *this;
  }

  String &operator=(String &&_other) noexcept {
    v_ = std::move(_other.v_);
    return *this;
  }

  // ACCESSORS
  String clone() const {
    String _out{};

    struct _CloneFrame {
      const String *_src;
      String *_dst;
    };

    std::vector<_CloneFrame> _stack{};
    _stack.reserve(8);
    _stack.push_back({this, &_out});
    while (!_stack.empty()) {
      auto _frame = _stack.back();
      _stack.pop_back();
      const String *_src = _frame._src;
      String *_dst = _frame._dst;
      if (std::holds_alternative<EmptyString>(_src->v())) {
        _dst->v_ = EmptyString{};
      } else {
        const auto &_alt = std::get<String0>(_src->v());
        _dst->v_ = String0{_alt.a0.clone(),
                           _alt.a1 ? std::make_shared<String>() : nullptr};
        auto &_dst_alt = std::get<String0>(_dst->v_);
        if (_alt.a1) {
          _stack.push_back({_alt.a1.get(), _dst_alt.a1.get()});
        }
      }
    }
    return _out;
  }

  // CREATORS
  static String emptystring() { return String(EmptyString{}); }

  static String string0(Ascii a0, String a1) {
    return String(
        String0{std::move(a0), std::make_shared<String>(std::move(a1))});
  }

  // MANIPULATORS
  ~String() {
    std::vector<std::shared_ptr<String>> _stack{};
    _stack.reserve(8);
    auto _drain = [&](String &_node) {
      if (std::holds_alternative<String0>(_node.v_)) {
        auto &_alt = std::get<String0>(_node.v_);
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

  String append(String s2) const {
    if (std::holds_alternative<typename String::EmptyString>(this->v())) {
      return s2;
    } else {
      const auto &[a0, a1] = std::get<typename String::String0>(this->v());
      return String::string0(a0, a1->append(std::move(s2)));
    }
  }

  Nat length() const {
    if (std::holds_alternative<typename String::EmptyString>(this->v())) {
      return Nat::o();
    } else {
      const auto &[a0, a1] = std::get<typename String::String0>(this->v());
      return Nat::s(a1->length());
    }
  }
};

struct Levenshtein {
  struct edit {
    // TYPES
    struct Insertion {
      Ascii a;
      String s;
    };

    struct Deletion {
      Ascii a;
      String s;
    };

    struct Update {
      Ascii a;
      Ascii a_1;
      String neq;
    };

    using variant_t = std::variant<Insertion, Deletion, Update>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    edit() {}

    explicit edit(Insertion _v) : v_(std::move(_v)) {}

    explicit edit(Deletion _v) : v_(std::move(_v)) {}

    explicit edit(Update _v) : v_(std::move(_v)) {}

    edit(const edit &_other) : v_(std::move(_other.clone().v_)) {}

    edit(edit &&_other) noexcept : v_(std::move(_other.v_)) {}

    edit &operator=(const edit &_other) {
      v_ = std::move(_other.clone().v_);
      return *this;
    }

    edit &operator=(edit &&_other) noexcept {
      v_ = std::move(_other.v_);
      return *this;
    }

    // ACCESSORS
    edit clone() const {
      if (std::holds_alternative<Insertion>(this->v())) {
        const auto &[a, s] = std::get<Insertion>(this->v());
        return edit(Insertion{a.clone(), s.clone()});
      } else if (std::holds_alternative<Deletion>(this->v())) {
        const auto &[a, s] = std::get<Deletion>(this->v());
        return edit(Deletion{a.clone(), s.clone()});
      } else {
        const auto &[a, a_1, neq] = std::get<Update>(this->v());
        return edit(Update{a.clone(), a_1.clone(), neq.clone()});
      }
    }

    // CREATORS
    static edit insertion(Ascii a, String s) {
      return edit(Insertion{std::move(a), std::move(s)});
    }

    static edit deletion(Ascii a, String s) {
      return edit(Deletion{std::move(a), std::move(s)});
    }

    static edit update(Ascii a, Ascii a_1, String neq) {
      return edit(Update{std::move(a), std::move(a_1), std::move(neq)});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    template <typename T1, typename F0, typename F1, typename F2>
      requires std::is_invocable_r_v<T1, F0 &, Ascii &, String &> &&
               std::is_invocable_r_v<T1, F1 &, Ascii &, String &> &&
               std::is_invocable_r_v<T1, F2 &, Ascii &, Ascii &, String &>
    T1 edit_rec(F0 &&f, F1 &&f0, F2 &&f1, const String &,
                const String &) const {
      if (std::holds_alternative<typename edit::Insertion>(this->v())) {
        const auto &[a0, s0] = std::get<typename edit::Insertion>(this->v());
        return f(a0, s0);
      } else if (std::holds_alternative<typename edit::Deletion>(this->v())) {
        const auto &[a0, s0] = std::get<typename edit::Deletion>(this->v());
        return f0(a0, s0);
      } else {
        const auto &[a0, a_1, neq] = std::get<typename edit::Update>(this->v());
        return f1(a0, a_1, neq);
      }
    }

    template <typename T1, typename F0, typename F1, typename F2>
      requires std::is_invocable_r_v<T1, F0 &, Ascii &, String &> &&
               std::is_invocable_r_v<T1, F1 &, Ascii &, String &> &&
               std::is_invocable_r_v<T1, F2 &, Ascii &, Ascii &, String &>
    T1 edit_rect(F0 &&f, F1 &&f0, F2 &&f1, const String &,
                 const String &) const {
      if (std::holds_alternative<typename edit::Insertion>(this->v())) {
        const auto &[a0, s0] = std::get<typename edit::Insertion>(this->v());
        return f(a0, s0);
      } else if (std::holds_alternative<typename edit::Deletion>(this->v())) {
        const auto &[a0, s0] = std::get<typename edit::Deletion>(this->v());
        return f0(a0, s0);
      } else {
        const auto &[a0, a_1, neq] = std::get<typename edit::Update>(this->v());
        return f1(a0, a_1, neq);
      }
    }
  };

  struct chain {
    // TYPES
    struct Empty {};

    struct Skip {
      Ascii a;
      String s;
      String t;
      Nat n;
      std::shared_ptr<chain> a4;
    };

    struct Change {
      String s;
      String t;
      String u;
      Nat n;
      edit a4;
      std::shared_ptr<chain> a5;
    };

    using variant_t = std::variant<Empty, Skip, Change>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    chain() {}

    explicit chain(Empty _v) : v_(_v) {}

    explicit chain(Skip _v) : v_(std::move(_v)) {}

    explicit chain(Change _v) : v_(std::move(_v)) {}

    chain(const chain &_other) : v_(std::move(_other.clone().v_)) {}

    chain(chain &&_other) noexcept : v_(std::move(_other.v_)) {}

    chain &operator=(const chain &_other) {
      v_ = std::move(_other.clone().v_);
      return *this;
    }

    chain &operator=(chain &&_other) noexcept {
      v_ = std::move(_other.v_);
      return *this;
    }

    // ACCESSORS
    chain clone() const {
      chain _out{};

      struct _CloneFrame {
        const chain *_src;
        chain *_dst;
      };

      std::vector<_CloneFrame> _stack{};
      _stack.reserve(8);
      _stack.push_back({this, &_out});
      while (!_stack.empty()) {
        auto _frame = _stack.back();
        _stack.pop_back();
        const chain *_src = _frame._src;
        chain *_dst = _frame._dst;
        if (std::holds_alternative<Empty>(_src->v())) {
          _dst->v_ = Empty{};
        } else if (std::holds_alternative<Skip>(_src->v())) {
          const auto &_alt = std::get<Skip>(_src->v());
          _dst->v_ = Skip{_alt.a.clone(), _alt.s.clone(), _alt.t.clone(),
                          _alt.n.clone(),
                          _alt.a4 ? std::make_shared<chain>() : nullptr};
          auto &_dst_alt = std::get<Skip>(_dst->v_);
          if (_alt.a4) {
            _stack.push_back({_alt.a4.get(), _dst_alt.a4.get()});
          }
        } else {
          const auto &_alt = std::get<Change>(_src->v());
          _dst->v_ = Change{
              _alt.s.clone(),  _alt.t.clone(),
              _alt.u.clone(),  _alt.n.clone(),
              _alt.a4.clone(), _alt.a5 ? std::make_shared<chain>() : nullptr};
          auto &_dst_alt = std::get<Change>(_dst->v_);
          if (_alt.a5) {
            _stack.push_back({_alt.a5.get(), _dst_alt.a5.get()});
          }
        }
      }
      return _out;
    }

    // CREATORS
    static chain empty() { return chain(Empty{}); }

    static chain skip(Ascii a, String s, String t, Nat n, chain a4) {
      return chain(Skip{std::move(a), std::move(s), std::move(t), std::move(n),
                        std::make_shared<chain>(std::move(a4))});
    }

    static chain change(String s, String t, String u, Nat n, edit a4,
                        chain a5) {
      return chain(Change{std::move(s), std::move(t), std::move(u),
                          std::move(n), std::move(a4),
                          std::make_shared<chain>(std::move(a5))});
    }

    // MANIPULATORS
    ~chain() {
      std::vector<std::shared_ptr<chain>> _stack{};
      _stack.reserve(8);
      auto _drain = [&](chain &_node) {
        if (std::holds_alternative<Skip>(_node.v_)) {
          auto &_alt = std::get<Skip>(_node.v_);
          if (_alt.a4) {
            _stack.push_back(std::move(_alt.a4));
          }
        }
        if (std::holds_alternative<Change>(_node.v_)) {
          auto &_alt = std::get<Change>(_node.v_);
          if (_alt.a5) {
            _stack.push_back(std::move(_alt.a5));
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

    chain aux_eq_char(const String &, const String &, const Ascii &, String xs,
                      Ascii y, String ys, Nat n) const {
      return chain::skip(std::move(y), std::move(xs), std::move(ys),
                         std::move(n), std::move(*this));
    }

    chain aux_update(const String &, const String &, const Ascii &x,
                     const String &xs, const Ascii &y, const String &ys,
                     const Nat &n) const {
      return this->update_chain(x, y, xs, ys, n);
    }

    chain aux_delete(const String &, const String &, const Ascii &x,
                     const String &xs, Ascii y, String ys, const Nat &n) const {
      return this->delete_chain(
          x, xs, String::string0(std::move(y), std::move(ys)), n);
    }

    chain aux_insert(const String &, const String &, Ascii x, String xs,
                     const Ascii &y, const String &ys, const Nat &n) const {
      return this->insert_chain(y, String::string0(std::move(x), std::move(xs)),
                                ys, n);
    }

    chain update_chain(Ascii c, Ascii c_, String s1, String s2, Nat n) const {
      return chain::change(String::string0(c, s1), String::string0(c_, s1),
                           String::string0(c_, s2), n, edit::update(c, c_, s1),
                           chain::skip(c_, s1, s2, n, std::move(*this)));
    }

    chain delete_chain(Ascii c, String s1, String s2, Nat n) const {
      return chain::change(String::string0(c, s1), s1, std::move(s2),
                           std::move(n), edit::deletion(c, s1),
                           std::move(*this));
    }

    chain insert_chain(Ascii c, String s1, String s2, Nat n) const {
      return chain::change(s1, String::string0(c, s1), String::string0(c, s2),
                           n, edit::insertion(c, s1),
                           chain::skip(c, s1, s2, n, std::move(*this)));
    }

    template <typename T1, typename F1, typename F2>
      requires std::is_invocable_r_v<T1, F1 &, Ascii &, String &, String &,
                                     Nat &, chain &, T1 &> &&
               std::is_invocable_r_v<T1, F2 &, String &, String &, String &,
                                     Nat &, edit &, chain &, T1 &>
    T1 chain_rec(T1 f, F1 &&f0, F2 &&f1, const String &, const String &,
                 const Nat &) const {
      if (std::holds_alternative<typename chain::Empty>(this->v())) {
        return f;
      } else if (std::holds_alternative<typename chain::Skip>(this->v())) {
        const auto &[a0, s0, t0, n0, a4] =
            std::get<typename chain::Skip>(this->v());
        return f0(a0, s0, t0, n0, *a4,
                  a4->template chain_rec<T1>(f, f0, f1, s0, t0, n0));
      } else {
        const auto &[s0, t0, u0, n0, a4, a5] =
            std::get<typename chain::Change>(this->v());
        return f1(s0, t0, u0, n0, a4, *a5,
                  a5->template chain_rec<T1>(f, f0, f1, t0, u0, n0));
      }
    }

    template <typename T1, typename F1, typename F2>
      requires std::is_invocable_r_v<T1, F1 &, Ascii &, String &, String &,
                                     Nat &, chain &, T1 &> &&
               std::is_invocable_r_v<T1, F2 &, String &, String &, String &,
                                     Nat &, edit &, chain &, T1 &>
    T1 chain_rect(T1 f, F1 &&f0, F2 &&f1, const String &, const String &,
                  const Nat &) const {
      if (std::holds_alternative<typename chain::Empty>(this->v())) {
        return f;
      } else if (std::holds_alternative<typename chain::Skip>(this->v())) {
        const auto &[a0, s0, t0, n0, a4] =
            std::get<typename chain::Skip>(this->v());
        return f0(a0, s0, t0, n0, *a4,
                  a4->template chain_rect<T1>(f, f0, f1, s0, t0, n0));
      } else {
        const auto &[s0, t0, u0, n0, a4, a5] =
            std::get<typename chain::Change>(this->v());
        return f1(s0, t0, u0, n0, a4, *a5,
                  a5->template chain_rect<T1>(f, f0, f1, t0, u0, n0));
      }
    }
  };

  static chain same_chain(const String &s);

  template <typename T1> static T1 _inserts_chain_F(const String s) {
    if (std::holds_alternative<typename String::EmptyString>(s.v())) {
      return chain::empty();
    } else {
      const auto &[a00, a10] = std::get<typename String::String0>(s.v());
      return chain::skip(a00, *a10, *a10, Nat::o(), _inserts_chain_F<T1>(*a10));
    }
  }

  static chain inserts_chain(const String &s1, const String &s2);
  static chain inserts_chain_empty(const String &s);
  static chain deletes_chain(const String &s1, const String &s2);
  static chain deletes_chain_empty(const String &s);
  static chain aux_both_empty(const String &_x, const String &_x0);

  template <typename T1, typename F3>
    requires std::is_invocable_r_v<Nat, F3 &, T1 &>
  static T1 min3_app(T1 x, T1 y, T1 z, F3 &&f) {
    Nat n1 = f(x);
    Nat n2 = f(y);
    Nat n3 = f(z);
    switch (n1.leb(n2)) {
    case Bool0::TRUE_: {
      switch (std::move(n1).leb(std::move(n3))) {
      case Bool0::TRUE_: {
        return x;
      }
      case Bool0::FALSE_: {
        return z;
      }
      default:
        std::unreachable();
      }
    }
    case Bool0::FALSE_: {
      switch (std::move(n2).leb(std::move(n3))) {
      case Bool0::TRUE_: {
        return y;
      }
      case Bool0::FALSE_: {
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

  static SigT<Nat, chain> levenshtein_chain(const String &s, String _x0);
  static Nat levenshtein_computed(const String &s, const String &t);
  static Nat levenshtein(const String &_x0, const String &_x1);
};

#endif // INCLUDED_LEVENSHTEIN
