#ifndef INCLUDED_LEVENSHTEIN
#define INCLUDED_LEVENSHTEIN

#include "crane_fn.h"
#include "obj.h"
#include "small_vector.h"
#include <atomic>
#include <memory>
#include <optional>
#include <stdexcept>
#include <type_traits>
#include <utility>
#include <variant>

enum class Bool0;
struct Nat;
template <typename A, typename P> struct SigT;
enum class Sumbool;
struct Ascii;
struct String;

struct Bool {
  static Sumbool bool_dec(Bool0 b1, Bool0 b2);
};
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

  static Nat o() { return Nat(O{}); }

  static Nat s(Nat a0) { return Nat(S{std::make_shared<Nat>(std::move(a0))}); }

  // MANIPULATORS
  ~Nat() {
    auto _next = [&](variant_t &_v) -> std::shared_ptr<Nat> {
      if (auto *_alt = std::get_if<S>(&_v)) {
        if (_alt->a0 && _alt->a0.use_count() == 1) {
          std::atomic_thread_fence(std::memory_order_acquire);
          return std::move(_alt->a0);
        }
      }
      return nullptr;
    };
    std::shared_ptr<Nat> _cur = _next(v_mut());
    while (_cur) {
      _cur = _next(_cur->v_mut());
    }
  }

  Nat(const Nat &) = default;
  Nat &operator=(const Nat &) = default;
  Nat(Nat &&) = default;
  Nat &operator=(Nat &&) = default;

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  Bool0 leb(const Nat &m) const {
    const Nat *_loop_self = this;
    const Nat *_loop_m = &m;
    while (true) {
      auto &&_sv = *_loop_self;
      if (std::holds_alternative<typename Nat::O>(_sv.v())) {
        return Bool0::TRUE_;
      } else {
        const auto &[a0] = std::get<typename Nat::S>(_sv.v());
        if (std::holds_alternative<typename Nat::O>(_loop_m->v())) {
          return Bool0::FALSE_;
        } else {
          const auto &[a00] = std::get<typename Nat::S>(_loop_m->v());
          _loop_self = crane_raw(a0);
          _loop_m = crane_raw(a00);
        }
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

  template <typename CraneU0, typename CraneU1>
  operator SigT<CraneU0, CraneU1>() const {
    return {[&]() -> CraneU0 {
              if constexpr (crane_convertible<CraneU0, const A &>) {
                return crane_convert<CraneU0>(x);
              } else {
                throw std::logic_error("unreachable: inactive constructor "
                                       "field at this instantiation");
              }
            }(),
            [&]() -> CraneU1 {
              if constexpr (crane_convertible<CraneU1, const P &>) {
                return crane_convert<CraneU1>(a1);
              } else {
                throw std::logic_error("unreachable: inactive constructor "
                                       "field at this instantiation");
              }
            }()};
  }

  // CREATORS
  static SigT<A, P> existt(A x, P a1) { return {std::move(x), std::move(a1)}; }

  A projT1() const {
    const auto &[x0, a1] = *this;
    return x0;
  }
};
enum class Sumbool { LEFT, RIGHT };

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

  Sumbool ascii_dec(const Ascii &b) const;
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

  static String emptystring() { return String(EmptyString{}); }

  static String string0(Ascii a0, String a1) {
    return String(
        String0{std::move(a0), std::make_shared<String>(std::move(a1))});
  }

  // MANIPULATORS
  ~String() {
    auto _next = [&](variant_t &_v) -> std::shared_ptr<String> {
      if (auto *_alt = std::get_if<String0>(&_v)) {
        if (_alt->a1 && _alt->a1.use_count() == 1) {
          std::atomic_thread_fence(std::memory_order_acquire);
          return std::move(_alt->a1);
        }
      }
      return nullptr;
    };
    std::shared_ptr<String> _cur = _next(v_mut());
    while (_cur) {
      _cur = _next(_cur->v_mut());
    }
  }

  String(const String &) = default;
  String &operator=(const String &) = default;
  String(String &&) = default;
  String &operator=(String &&) = default;

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  String append(String s2) const;

  Nat length() const {
    std::optional<Nat> _root{};
    std::shared_ptr<Nat> *_write = nullptr;
    const String *_loop_self = this;
    while (true) {
      auto &&_sv = *_loop_self;
      if (std::holds_alternative<typename String::EmptyString>(_sv.v())) {
        auto _value = Nat::o();
        (_write ? *(*_write = std::make_shared<Nat>(std::move(_value)))
                : _root.emplace(std::move(_value)));
        break;
      } else {
        const auto &[a0, a1] = std::get<typename String::String0>(_sv.v());
        auto _cell = typename Nat::S(nullptr);
        Nat &_node =
            (_write ? *(*_write = std::make_shared<Nat>(std::move(_cell)))
                    : _root.emplace(std::move(_cell)));
        _write = &std::get<typename Nat::S>(_node.v_mut()).a0;
        _loop_self = crane_raw(a1);
        continue;
      }
    }
    return std::move(*_root);
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
    T1 edit_rec(F0 &&f, F1 &&f0, F2 &&f1, const String &_x,
                const String &_x0) const {
      return this->template edit_rect<T1>(f, f0, f1, _x, _x0);
    }

    template <typename T1, typename F0, typename F1, typename F2>
      requires std::is_invocable_r_v<T1, F0 &, const Ascii &, const String &> &&
               std::is_invocable_r_v<T1, F1 &, const Ascii &, const String &> &&
               std::is_invocable_r_v<T1, F2 &, const Ascii &, const Ascii &,
                                     const String &>
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
      auto _next = [&](variant_t &_v) -> std::shared_ptr<chain> {
        if (auto *_alt = std::get_if<Skip>(&_v)) {
          if (_alt->a4 && _alt->a4.use_count() == 1) {
            std::atomic_thread_fence(std::memory_order_acquire);
            return std::move(_alt->a4);
          }
        }
        if (auto *_alt = std::get_if<Change>(&_v)) {
          if (_alt->a5 && _alt->a5.use_count() == 1) {
            std::atomic_thread_fence(std::memory_order_acquire);
            return std::move(_alt->a5);
          }
        }
        return nullptr;
      };
      std::shared_ptr<chain> _cur = _next(v_mut());
      while (_cur) {
        _cur = _next(_cur->v_mut());
      }
    }

    chain(const chain &) = default;
    chain &operator=(const chain &) = default;
    chain(chain &&) = default;
    chain &operator=(chain &&) = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    chain aux_eq_char(const String &, const String &, const Ascii &,
                      const String &xs, const Ascii &y, const String &ys,
                      const Nat &n) const {
      return chain::skip(y, xs, ys, n, *this);
    }

    chain aux_update(const String &, const String &, const Ascii &x,
                     const String &xs, const Ascii &y, const String &ys,
                     const Nat &n) const {
      return this->update_chain(x, y, xs, ys, n);
    }

    chain aux_delete(const String &, const String &, const Ascii &x,
                     const String &xs, const Ascii &y, const String &ys,
                     const Nat &n) const {
      return this->delete_chain(x, xs, String::string0(y, ys), n);
    }

    chain aux_insert(const String &, const String &, const Ascii &x,
                     const String &xs, const Ascii &y, const String &ys,
                     const Nat &n) const {
      return this->insert_chain(y, String::string0(x, xs), ys, n);
    }

    chain update_chain(const Ascii &c, const Ascii &c_, const String &s1,
                       const String &s2, const Nat &n) const {
      return chain::change(String::string0(c, s1), String::string0(c_, s1),
                           String::string0(c_, s2), n, edit::update(c, c_, s1),
                           chain::skip(c_, s1, s2, n, *this));
    }

    chain delete_chain(const Ascii &c, const String &s1, const String &s2,
                       const Nat &n) const {
      return chain::change(String::string0(c, s1), s1, s2, n,
                           edit::deletion(c, s1), *this);
    }

    chain insert_chain(const Ascii &c, const String &s1, const String &s2,
                       const Nat &n) const {
      return chain::change(s1, String::string0(c, s1), String::string0(c, s2),
                           n, edit::insertion(c, s1),
                           chain::skip(c, s1, s2, n, *this));
    }

    template <typename T1, typename F1, typename F2>
    T1 chain_rec(const T1 &f, F1 &&f0, F2 &&f1, const String &_x,
                 const String &_x0, const Nat &_x1) const {
      return this->template chain_rect<T1>(f, f0, f1, _x, _x0, _x1);
    }

    template <typename T1, typename F1, typename F2>
    T1 chain_rect(T1 f, F1 &&f0, F2 &&f1, const String &_x, const String &_x0,
                  const Nat &_x1) const {
      const chain *_self = this;

      /// CraneEnter: captures varying parameters for each recursive call.
      struct CraneEnter {
        const chain *_self;
        String _x;
        String _x0;
        Nat _x1;
      };

      /// CraneCont_Change: saves [a4, a5, n0, s0, t0, u0], resumes after
      /// recursive call, then processes rest.
      struct CraneCont_Change {
        edit a4;
        std::shared_ptr<chain> a5;
        Nat n0;
        String s0;
        String t0;
        String u0;
      };

      /// CraneCont_Skip: saves [a0, a4, n0, s0, t0], resumes after recursive
      /// call, then processes rest.
      struct CraneCont_Skip {
        Ascii a0;
        std::shared_ptr<chain> a4;
        Nat n0;
        String s0;
        String t0;
      };

      using CraneFrame =
          std::variant<CraneEnter, CraneCont_Change, CraneCont_Skip>;
      T1 _result{};
      crane::small_vector<CraneFrame> _stack;
      _stack.emplace_back(CraneEnter{_self, _x, _x0, _x1});
      /// Loopified chain_rect: CraneEnter -> CraneCont_Change ->
      /// CraneCont_Skip.
      while (!_stack.empty()) {
        CraneFrame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<CraneEnter>(_frame)) {
          auto _f = std::move(std::get<CraneEnter>(_frame));
          const chain *_self = _f._self;
          const String &_x = std::move(_f._x);
          const String &_x0 = std::move(_f._x0);
          const Nat &_x1 = std::move(_f._x1);
          auto &&_sv = *_self;
          if (std::holds_alternative<typename chain::Empty>(_sv.v())) {
            _result = f;
          } else if (std::holds_alternative<typename chain::Skip>(_sv.v())) {
            const auto &[a0, s0, t0, n0, a4] =
                std::get<typename chain::Skip>(_sv.v());
            _stack.emplace_back(CraneCont_Skip{a0, a4, n0, s0, t0});
            _stack.emplace_back(CraneEnter{crane_raw(a4), s0, t0, n0});
          } else {
            const auto &[s0, t0, u0, n0, a4, a5] =
                std::get<typename chain::Change>(_sv.v());
            _stack.emplace_back(CraneCont_Change{a4, a5, n0, s0, t0, u0});
            _stack.emplace_back(CraneEnter{crane_raw(a5), t0, u0, n0});
          }
        } else if (std::holds_alternative<CraneCont_Change>(_frame)) {
          auto _f = std::move(std::get<CraneCont_Change>(_frame));
          edit a4 = std::move(_f.a4);
          std::shared_ptr<chain> a5 = std::move(_f.a5);
          Nat n0 = std::move(_f.n0);
          String s0 = std::move(_f.s0);
          String t0 = std::move(_f.t0);
          String u0 = std::move(_f.u0);
          _result = f1(s0, t0, u0, n0, a4, *a5, std::move(_result));
        } else {
          auto _f = std::move(std::get<CraneCont_Skip>(_frame));
          Ascii a0 = std::move(_f.a0);
          std::shared_ptr<chain> a4 = std::move(_f.a4);
          Nat n0 = std::move(_f.n0);
          String s0 = std::move(_f.s0);
          String t0 = std::move(_f.t0);
          _result = f0(a0, s0, t0, n0, *a4, std::move(_result));
        }
      }
      return _result;
    }
  };

  static chain same_chain(const String &s);
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
      break;
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
      break;
    }
    default:
      std::unreachable();
    }
  }

  static SigT<Nat, chain> levenshtein_chain(const String &s, String x0_);
  static Nat levenshtein_computed(const String &s, const String &t);
  static Nat levenshtein(const String &x0_, const String &x1_);
};

inline Sumbool Ascii::ascii_dec(const Ascii &b) const {
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
                break;
              }
              case Sumbool::RIGHT: {
                return Sumbool::RIGHT;
              }
              default:
                std::unreachable();
              }
              break;
            }
            case Sumbool::RIGHT: {
              return Sumbool::RIGHT;
            }
            default:
              std::unreachable();
            }
            break;
          }
          case Sumbool::RIGHT: {
            return Sumbool::RIGHT;
          }
          default:
            std::unreachable();
          }
          break;
        }
        case Sumbool::RIGHT: {
          return Sumbool::RIGHT;
        }
        default:
          std::unreachable();
        }
        break;
      }
      case Sumbool::RIGHT: {
        return Sumbool::RIGHT;
      }
      default:
        std::unreachable();
      }
      break;
    }
    case Sumbool::RIGHT: {
      return Sumbool::RIGHT;
    }
    default:
      std::unreachable();
    }
    break;
  }
  case Sumbool::RIGHT: {
    return Sumbool::RIGHT;
  }
  default:
    std::unreachable();
  }
}

inline String String::append(String s2) const {
  if (std::holds_alternative<typename String::EmptyString>(this->v())) {
    return s2;
  } else {
    const auto &[a0, a1] = std::get<typename String::String0>(this->v());
    return String::string0(a0, a1->append(std::move(s2)));
  }
}

#endif // INCLUDED_LEVENSHTEIN
